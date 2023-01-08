package main

import (
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
	"testing"
)

func setRing() *ring.Ring {
	n := uint32(64)
	q := bigint.NewIntFromString("257")
	nttParams := polynomial.GenerateNTTParams(n, *q)

	r := new(ring.Ring)
	r.N = uint32(64)
	r.Q = *q
	r.Poly, _ = polynomial.NewPolynomial(n, *q, nttParams)
	return r
}

func TestRingMatAdd(t *testing.T) {
	n := uint32(64)

	col := uint32(3)
	row := uint32(2)

	r := setRing()
	coeffs := make([]bigint.Int, n)
	coeffs[0].SetInt(int64(2))

	m, _ := NewRingMartix(col, row, nil)
	var i, j uint32
	for i = 0; i < col; i++ {
		for j = 0; j < row; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)
			m.ringvectors[i].rings[j] = *tmp
		}
	}
	_, _ = m.RingMatAdd(m, m)
	exp := coeffs[0].Lsh(&coeffs[0], 1)

	for i = 0; i < col; i++ {
		for j = 0; j < row; j++ {
			c0 := m.ringvectors[i].rings[j].Poly.GetCoefficients()[0]
			if c0.Compare(exp) != 0 {
				t.Errorf("FAIL: [TestRingMatAdd] expected %v but got %v.", coeffs[0], c0)
				return
			}
		}
	}
}

func TestRingMatMul(t *testing.T) {
	setTestSettings()

	one := uint32(1)
	two := uint32(2)
	val1 := int64(4)
	val2 := int64(9)
	var exp bigint.Int
	exp.SetInt(2 * val1 * val2)

	r := setRing()
	coeffs := make([]bigint.Int, settings.d)

	m1, _ := NewRingMartix(one, two, settings.nttParams)
	m1.SetRingMartix(r)
	m2, _ := NewRingMartix(two, one, settings.nttParams)
	m2.SetRingMartix(r)
	m, _ := NewRingMartix(one, one, settings.nttParams)
	m.SetRingMartix(r)
	var i, j uint32
	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			coeffs[0].SetInt(val1)
			_ = m1.ringvectors[i].rings[j].Poly.SetCoefficients(coeffs)
			coeffs[0].SetInt(val2)
			_ = m2.ringvectors[j].rings[i].Poly.SetCoefficients(coeffs)
		}
	}

	_, _ = m.RingMatMul(m1, m2)
	c0 := m.ringvectors[0].rings[0].Poly.GetCoefficients()[0]
	if c0.Compare(&exp) != 0 {
		t.Errorf("FAIL: [TestRingMatMul] expected %v but got %v.", exp, c0)
		return
	}
}

func TestRingMatIsEqual(t *testing.T) {
	setTestSettings()

	one := uint32(1)
	two := uint32(2)

	r := setRing()
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(2))

	m1, _ := NewRingMartix(one, two, nil)
	m2, _ := NewRingMartix(one, two, nil)
	var i, j uint32
	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)

			m1.ringvectors[i].rings[j] = *tmp
		}
	}

	for i = 0; i < one; i++ {
		for j = 0; j < two; j++ {
			tmp, _ := ring.CopyRing(r)
			_ = tmp.Poly.SetCoefficients(coeffs)

			m2.ringvectors[i].rings[j] = *tmp
		}
	}

	if !m1.RingMatIsEqual(m2) {
		t.Errorf("FAIL: [TestRingMatIsEqual] should be same.")
		return
	}

	coeffs[0].SetInt(int64(1))
	_ = m2.ringvectors[m2.col-1].rings[m2.row-1].Poly.SetCoefficients(coeffs)

	if m1.RingMatIsEqual(m2) {
		t.Errorf("FAIL: [TestRingMatIsEqual] should not be same.")
		return
	}
}
