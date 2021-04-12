package main

import (
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
	"testing"
)

// helper functions

func setBalanceSetting(M, S uint32) (Ga, Gb *RingMartix, Av, amtin []RingMartix, vout []uint64) {
	setTestSettings()

	outvalue := uint64(1)
	invalue := outvalue * uint64(S) / uint64(M)

	va := settings.precision
	vb := 2 * settings.precision * (S + 1) - 2
	Ga, _ = SamMat(va, 0)
	Gb, _ = SamMat(vb, 0)

	Av = make([]RingMartix, M)
	amtin = make([]RingMartix, M)
	for i := range Av {
		Avtmp, _, amttmp, _ := Mint(Ga, invalue)
		Av[i] = *Avtmp
		amtin[i] = *amttmp
	}

	vout = make([]uint64, S)
	for i := range vout {
		vout[i] = outvalue
	}

	return
}

func setOneOutOfManySetting(beta, k, l uint32) (Ga, Gb, pr *RingMartix, Pv []RingMartix) {
	setTestSettings()
	N := 1
	for i := 0; i < int(k); i++ {
		N = N * int(beta)
	}

	r := new(ring.Ring)
	r.N = settings.d
	r.Q = settings.q
	r.Poly, _ = polynomial.NewPolynomial(settings.d, settings.q, settings.nttParams)

	va := beta
	vb := k * va + settings.m
	Ga, _ = SamMat(va, 0)
	Gb, _ = SamMat(vb, 0)

	Pv = make([]RingMartix, N)
	rv := make([]RingMartix, N)

	zero, _ := NewRingMartix(beta, 1, settings.nttParams)
	zero.SetZeroRingMartix(r, settings.d)

	for i := 0; i < N; i++ {
		Pui, pri, _ := Commitment(Ga, zero, 10)
		Pv[i] = *Pui
		rv[i] = *pri
	}

	pr = &rv[l]
	return
}

// functional tests

func TestBalanceProof(t *testing.T) {
	for i := 0; i < 2; i++ {
		M := uint32(1)
		S := uint32(i + 1)

		Ga, Gb, Av, amtin, vout := setBalanceSetting(M, S)

		ComB, ComC, f, zb, zc, Bv, zoutv, x, _:= BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
		result, err:= BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)

		if err != nil {
			t.Errorf("Error: [TestBalanceProof] at M=%v, S=%v. %s", M, S, err)
			return
		}

		if !result {
			t.Errorf("FAIL: [TestBalanceProof] at M=%v, S=%v.", M, S)
			return
		}
	}
}

func TestOneOutOfManyProof(t *testing.T) {
	bv :=[]uint32 {2, 8, 16, 32, 3}
	kv :=[]uint32 {1, 1, 1, 1, 4}
	l := uint32(0)

	for i := range bv {
		Ga, Gb, pr, Pv := setOneOutOfManySetting(bv[i], kv[i], l)

		ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, kv[i], bv[i], Pv, 20, 14)
		result, err := OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)

		if err != nil {
			t.Errorf("Error: [TestOneOutOfManyProof] at k=%v, beta=%v. %s", kv[i], bv[i], err)
			return
		}

		if !result {
			t.Errorf("FAIL: [TestOneOutOfManyProof] at k=%v, beta=%v.", kv[i], bv[i])
			return
		}
	}
}

// performance tests

// M = 1; S = 1
func BenchmarkBalanceProofM1S1(b *testing.B) {
	b.ResetTimer()
	M := uint32(1)
	S := uint32(1)

	Ga, Gb, Av, amtin, vout := setBalanceSetting(M, S)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _, _, _ = BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
			//_, _, _, _, _, _, _, _, _, _, _ = BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
		}
	})
}
// M = 1; S = 1
func BenchmarkBalanceVerifyM1S1(b *testing.B) {
	b.ResetTimer()
	setTestSettings()
	M := uint32(1)
	S := uint32(1)

	Ga, Gb, Av, amtin, vout := setBalanceSetting(M, S)

	ComB, ComC, f, zb, zc, Bv, zoutv, x, _:= BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
	//ComB, ComC, f, zb, zc, Bv, zoutv, x, _, _, _ := BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)
			//_, _, _, _ = BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)
		}
	})
}
// M = 1; S = 2
func BenchmarkBalanceProofM1S2(b *testing.B) {
	b.ResetTimer()
	M := uint32(1)
	S := uint32(2)

	Ga, Gb, Av, amtin, vout := setBalanceSetting(M, S)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _, _, _ = BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
			//_, _, _, _, _, _, _, _, _, _, _ = BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
		}
	})
}
// M = 1; S = 2
func BenchmarkBalanceVerifyM1S2(b *testing.B) {
	b.ResetTimer()
	setTestSettings()
	M := uint32(1)
	S := uint32(2)

	Ga, Gb, Av, amtin, vout := setBalanceSetting(M, S)

	ComB, ComC, f, zb, zc, Bv, zoutv, x, _:= BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)
	//ComB, ComC, f, zb, zc, Bv, zoutv, x, _, _, _ := BalanceProof(Ga, Gb, Av, amtin, vout, 20, 14, 2)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)
			//_, _, _, _ = BalanceVerify(Ga, Gb, ComB, ComC, f, zb, zc, Av, Bv, zoutv, x)
		}
	})
}


// N = 2; beta = 2; k = 1
func BenchmarkOneOutOfManyProofN2(b *testing.B) {
	b.ResetTimer()

	beta := uint32(2)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _ = OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)
		}
	})
}
// N = 2; beta = 2; k = 1
func BenchmarkOneOutOfManyVerifyN2(b *testing.B) {
	b.ResetTimer()

	beta := uint32(2)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)
		}
	})
}
// N = 8; beta = 8; k = 1
func BenchmarkOneOutOfManyProofN8(b *testing.B) {
	b.ResetTimer()

	beta := uint32(8)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _ = OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)
		}
	})
}
// N = 8; beta = 8; k = 1
func BenchmarkOneOutOfManyVerifyN8(b *testing.B) {
	b.ResetTimer()

	beta := uint32(8)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)
		}
	})
}
// N = 16; beta = 16; k = 1
func BenchmarkOneOutOfManyProofN16(b *testing.B) {
	b.ResetTimer()

	beta := uint32(16)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _ = OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)
		}
	})
}
// N = 16; beta = 16; k = 1
func BenchmarkOneOutOfManyVerifyN16(b *testing.B) {
	b.ResetTimer()

	beta := uint32(16)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)
		}
	})
}
// N = 32; beta = 32; k = 1
func BenchmarkOneOutOfManyProofN32(b *testing.B) {
	b.ResetTimer()

	beta := uint32(32)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _ = OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)
		}
	})
}
// N = 32; beta = 32; k = 1
func BenchmarkOneOutOfManyVerifyN32(b *testing.B) {
	b.ResetTimer()

	beta := uint32(32)
	k := uint32(1)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)
		}
	})
}
// N = 64; beta = 4; k = 3
func BenchmarkOneOutOfManyProofN64(b *testing.B) {
	b.ResetTimer()

	beta := uint32(4)
	k := uint32(3)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _, _, _, _, _, _ = OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)
		}
	})
}
// N = 64; beta = 4; k = 3
func BenchmarkOneOutOfManyVerifyN64(b *testing.B) {
	b.ResetTimer()

	beta := uint32(4)
	k := uint32(3)
	l := uint32(0)

	Ga, Gb, pr, Pv := setOneOutOfManySetting(beta, k, l)

	ComB, f, zb, zr, Ev, x, _ := OneOutOfManyProof(Ga, Gb, pr, l, k, beta, Pv, 20, 14)

	b.ReportAllocs()
	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_, _ = OneOutOfManyVerify(Ga, Gb, ComB, f, zb, zr, Pv, Ev, x)
		}
	})
}