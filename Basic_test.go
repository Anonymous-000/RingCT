package main

import (
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
	"testing"
)


func setTestSettings() {
	d := uint32(64)
	n := uint32(32)
	m := uint32(64)
	w := uint32(56)
	//q := bigint.NewIntFromString("8865920799731713")	// polynomial.GenerateNTTParams(d, q) never return, may due to factorization
	//q := bigint.NewIntFromString("2147221513")		// Not NTT friendly (N != 1 mod 2*d)
	//q := bigint.NewIntFromString("257")				// Fermat number (F3)
	q := bigint.NewIntFromString("65537")			// Fermat number (F4) (no big performance difference with F3)
	SetSettings(d, n, m, w, 64, *q, 8, 1, false)
}

func TestHash(t *testing.T) {
	setTestSettings()
	r1 := new(ring.Ring)
	r1.N = settings.d
	r1.Q = settings.q
	r1.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, nil)
	r2 := new(ring.Ring)
	r2, err := ring.CopyRing(r1)

	if err != nil {
		t.Errorf("Error: [TestHash] %s", err)
		return
	}

	msg := make([]byte, 2)
	msg[0] = 'M'
	msg[1] = 'G'

	Hash(msg, r1)
	Hash(msg, r2)

	cor1 := r1.Poly.GetCoefficients()
	cor2 := r1.Poly.GetCoefficients()
	for i := range cor1 {
		if !cor1[i].EqualTo(&cor2[i]) {
			t.Errorf("FAIL: [TestHash] Hashed values are not same: cor1[%v]: %v, cor2[%v]: %v.", i, cor1[i], i, cor2[i])
			return
		}
	}
}

func TestMint(t *testing.T) {
	setTestSettings()
	amt := uint64(5)
	coeffs := make([]bigint.Int, settings.d)
	coeffs[0].SetInt(int64(1))
	v := settings.precision + settings.m

	bits, _ := ConvertIntToRingBits(amt, settings.d, settings.precision, settings.q, settings.nttParams)
	G, _ := SamMat(v, 0)
	B, r, mbits, _ := Mint(G, amt)

	y, _ := ring.CopyRing(&G.ringvectors[0].rings[0])
	_ = y.Poly.SetCoefficients(coeffs)

	if !Open(G, B, bits, r, y) {
		t.Errorf("FAIL: [TestMint] Open failed.")
		return
	}

	if !mbits.RingMatIsEqual(bits) {
		t.Errorf("FAIL: [TestMint] randoms are different.")
		return
	}
}

func TestGenerateDelta(t *testing.T) {
	setTestSettings()
	v := MakeDeltaMatrix(7, 2, 3)
	for i := range v {
		fmt.Printf("--- delta_%v ---\n", i)
		v[i].ShowMatrix(settings.d)
	}
}

func TestMakePij(t *testing.T) {
	setTestSettings()
	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	coeffs := make([]bigint.Int, settings.d)
	a := make([]ring.Ring, 3)
	delta := make([]ring.Ring, 3)
	for i := range a {
		coeffs[0].SetInt(int64(i + 1))
		tmpring, _ := ring.CopyRing(r)
		_ = tmpring.Poly.SetCoefficients(coeffs)
		a[i] = *tmpring
		coeffs[0].SetInt(int64(i + 2))
		tmpring2, _ := ring.CopyRing(r)
		_ = tmpring2.Poly.SetCoefficients(coeffs)
		delta[i] = *tmpring2
	}

	piv := MakePij(a, delta)

	ShowRingVector(piv, settings.d)
}