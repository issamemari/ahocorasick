// ahocorasick.go: implementation of the Aho-Corasick string matching
// algorithm. Actually implemented as matching against []byte rather
// than the Go string type. Throughout this code []byte is referred to
// as a blice.
//
// http://en.wikipedia.org/wiki/Aho%E2%80%93Corasick_string_matching_algorithm
//
// Copyright (c) 2013 CloudFlare, Inc.

package ahocorasick

import (
	"container/list"
	"sync"
	"sync/atomic"
)

// A node in the trie structure used to implement Aho-Corasick
type node struct {
	root bool // true if this is the root

	b []byte // The blice at this node

	output bool // True means this node represents a blice that should
	// be output when matching
	index int // index into original dictionary if output is true

	counter uint64 // Set to the value of the Matcher.counter when a
	// match is output to prevent duplicate output

	child map[byte]*node
	// index represents a byte value which can be
	// appended to the current node. Blices in the
	// trie are built up byte by byte through these
	// child node pointers.

	suffix *node // Pointer to the longest possible strict suffix of
	// this node

	fail        *node // Pointer to the next node which is in the dictionary
	inverseFail []*node
	// which can be reached from here following suffixes. Called fail
	// because it is used to fallback in the trie when a match fails.
}

// Matcher is returned by NewMatcher and contains a list of blices to
// match against
type Matcher struct {
	counter uint64 // Counts the number of matches done, and is used to
	// prevent output of multiple matches of the same string
	dictionary [][]byte
	trie       []node // preallocated block of memory containing all the
	// nodes
	extent int   // offset into trie that is currently free
	root   *node // Points to trie[0]

	heap sync.Pool // a pool of haystacks to de-duplicate results in
	// a thread-safe manner
}

// Hit describes a match.
type Hit struct {
	// the index in the original dict of the keyword that was found.
	Index int
	// the start index in the text where the keyword was found.
	TextIndex int
}

// findBlice looks for a blice in the trie starting from the root and
// returns a pointer to the node representing the end of the blice. If
// the blice is not found it returns nil.
func (m *Matcher) findBlice(b []byte) *node {
	n := &m.trie[0]

	for n != nil && len(b) > 0 {
		n = n.child[b[0]]
		b = b[1:]
	}

	return n
}

// getFreeNode: gets a free node structure from the Matcher's trie
// pool and updates the extent to point to the next free node.
func (m *Matcher) getFreeNode() *node {
	m.extent += 1

	if m.extent == 1 {
		m.root = &m.trie[0]
		m.root.root = true
	}

	if m.extent > len(m.trie) {
		m.trie = append(m.trie, node{})
	}

	m.trie[m.extent-1].child = make(map[byte]*node, 0)
	m.trie[m.extent-1].inverseFail = make([]*node, 0)

	return &m.trie[m.extent-1]
}

func (m *Matcher) addBlice(blice []byte) (*node, []*node) {
	n := m.root
	var path []byte
	newNodes := make([]*node, 0)
	for _, b := range blice {
		path = append(path, b)

		c := n.child[b]

		if c == nil {
			c = m.getFreeNode()
			n.child[b] = c
			c.b = make([]byte, len(path))
			copy(c.b, path)

			newNodes = append(newNodes, c)

			// Nodes directly under the root node will have the
			// root as their fail point as there are no suffixes
			// possible.

			if len(path) == 1 {
				c.fail = m.root
			}

			c.suffix = m.root
		}

		n = c
	}
	if len(newNodes) == 0 {
		newNodes = append(newNodes, n)
	}
	return n, newNodes
}

// buildTrie builds the fundamental trie structure from a set of
// blices.
func (m *Matcher) buildTrie(dictionary [][]byte) {

	m.dictionary = dictionary
	// Work out the maximum size for the trie (all dictionary entries
	// are distinct plus the root). This is used to preallocate memory
	// for it.
	max := 1
	for _, blice := range dictionary {
		max += len(blice)
	}
	m.trie = make([]node, max)

	// Calling this an ignoring its argument simply allocated
	// m.trie[0] which will be the root element
	m.getFreeNode()

	// This loop builds the nodes in the trie by following through
	// each dictionary entry building the children pointers.
	for i, blice := range dictionary {
		n, _ := m.addBlice(blice)

		// m.addBlice returns a the final node representing a dictionary entry
		n.output = true
		n.index = i
	}

	l := new(list.List)
	l.PushBack(m.root)

	for l.Len() > 0 {
		n := l.Remove(l.Front()).(*node)
		for i := 0; i < 256; i++ {
			c := n.child[byte(i)]
			if c != nil {
				l.PushBack(c)
				m.setFailLinks(c)
			}
		}
	}
	m.trie = m.trie[:m.extent]
}

func (m *Matcher) setFailLinks(c *node) {
	var s *node
	for j := 1; j < len(c.b); j++ {
		s = m.findBlice(c.b[j:])
		if s != nil {
			break
		}
	}
	if s == nil {
		c.fail = m.root
		m.root.inverseFail = append(m.root.inverseFail, c)
	} else {
		c.fail = s
		s.inverseFail = append(s.inverseFail, c)
		if s.output {
			c.suffix = s
		}
	}
}

func (m *Matcher) AddString(s string) {
	m.AddBytes([]byte(s))
}

func (m *Matcher) AddBytes(blice []byte) {
	n := m.root
	n, newNodes := m.addBlice(blice)
	n.output = true
	n.index = len(m.dictionary)
	m.dictionary = append(m.dictionary, blice)

	for _, c := range newNodes {
		m.setFailLinks(c)
	}

	for _, n := range newNodes {
		parent := m.findBlice(n.b[:len(n.b)-1])
		l := new(list.List)
		for _, cc := range parent.inverseFail {
			l.PushBack(cc)
		}
		for l.Len() > 0 {
			c := l.Remove(l.Front()).(*node)
			for _, cc := range c.inverseFail {
				l.PushBack(cc)
			}
			tr := c.child[n.b[len(n.b)-1]]
			if tr != nil {
				// remove from inverse fail
				for i, cc := range tr.fail.inverseFail {
					if cc == tr.fail {
						tr.fail.inverseFail = append(tr.fail.inverseFail[:i], tr.fail.inverseFail[i+1:]...)
						break
					}
				}
				m.setFailLinks(tr)
			}
		}
	}
}

// NewMatcher creates a new Matcher used to match against a set of
// blices
func NewMatcher(dictionary [][]byte) *Matcher {
	m := new(Matcher)
	m.buildTrie(dictionary)
	return m
}

// NewStringMatcher creates a new Matcher used to match against a set
// of strings (this is a helper to make initialization easy)
func NewStringMatcher(dictionary []string) *Matcher {
	m := new(Matcher)
	var d [][]byte
	for _, s := range dictionary {
		d = append(d, []byte(s))
	}
	m.buildTrie(d)
	return m
}

// Match searches in for blices and returns all the blices found as indexes into
// the original dictionary.
//
// This is not thread-safe method, seek for MatchThreadSafe() instead.
func (m *Matcher) Match(in []byte) []Hit {
	m.counter++
	return match(in, m.root, m.dictionary, func(f *node) bool {
		if f.counter != m.counter {
			f.counter = m.counter
			return true
		}
		return false
	})
}

// match is a core of matching logic. Accepts input byte slice, starting node
// and a func to check whether should we include result into response or not
func match(in []byte, n *node, dictionary [][]byte, unique func(f *node) bool) []Hit {
	var hits []Hit
	for i, b := range in {
		c := b

		if !n.root && n.child[c] == nil {
			for n.child[byte(c)] == nil && !n.root {
				n = n.fail
			}
		}

		if n.child[c] != nil {
			f := n.child[c]
			n = f

			if f.output {
				if unique(f) {
					hit := Hit{Index: f.index, TextIndex: i - len(dictionary[f.index]) + 1}
					hits = append(hits, hit)
				}
			}

			for !f.suffix.root {
				f = f.suffix
				if unique(f) {
					hit := Hit{Index: f.index, TextIndex: i - len(dictionary[f.index]) + 1}
					hits = append(hits, hit)
				} else {

					// There's no point working our way up the
					// suffixes if it's been done before for this call
					// to Match. The matches are already in hits.

					break
				}
			}
		}
	}

	return hits
}

// MatchThreadSafe provides the same result as Match() but does it in a
// thread-safe manner. Uses a sync.Pool of haystacks to track the uniqueness of
// the result items.
func (m *Matcher) MatchThreadSafe(in []byte) []Hit {
	var (
		heap map[int]uint64
	)

	generation := atomic.AddUint64(&m.counter, 1)
	n := m.root
	// read the matcher's heap
	item := m.heap.Get()
	if item == nil {
		heap = make(map[int]uint64, len(m.trie))
	} else {
		heap = item.(map[int]uint64)
	}

	hits := match(in, n, m.dictionary, func(f *node) bool {
		g := heap[f.index]
		if g != generation {
			heap[f.index] = generation
			return true
		}
		return false
	})

	m.heap.Put(heap)
	return hits
}

// Contains returns true if any string matches. This can be faster
// than Match() when you do not need to know which words matched.
func (m *Matcher) Contains(in []byte) bool {
	n := m.root
	for _, b := range in {
		c := b
		if !n.root {
			for n.child[byte(c)] == nil && !n.root {
				n = n.fail
			}
		}

		if n.child[c] != nil {
			f := n.child[c]
			n = f

			if f.output {
				return true
			}

			for !f.suffix.root {
				return true
			}
		}
	}
	return false
}
