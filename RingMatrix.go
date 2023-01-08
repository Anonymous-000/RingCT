package main

import (
	"errors"
	"fmt"
	"github.com/dedis/lago/bigint"
	"github.com/dedis/lago/polynomial"
	"github.com/dedis/lago/ring"
	"math/rand"
)

type RingVector struct {
	rings     []ring.Ring
	nttParams *polynomial.NttParams
}

type RingMartix struct {
	ringvectors []RingVector
	col         uint32
	row         uint32
	nttParams   *polynomial.NttParams
}

// MulPoly cannot handle same inputs (but we fix this bug in local file)
// true indicates the bug exists
// false indicates the bug is fixed
var MulPolyBug = false

func NewRingMartix(col, row uint32, nttParams *polynomial.NttParams) (*RingMartix, error) {
	if col == 0 || row == 0 {
		return nil, nil
	}

	p := &RingMartix{make([]RingVector, col), col, row, nttParams}
	for i := range p.ringvectors {
		p.ringvectors[i] = RingVector{make([]ring.Ring, row), nttParams}
	}

	return p, nil
}

// Generate d random big ints in [-B, B].
// single = true: only set random[0]
// single = false: set all random[i]'s
func RqRandomB(seed int64, d uint32, B int, single bool) []bigint.Int {
	random := make([]bigint.Int, d)
	var i uint32
	rand.Seed(seed)

	r := rand.Intn(2*B + 1)
	r = r - B
	random[0].SetInt(int64(r))
	random[0].Mod(&random[0], &settings.q)

	for i = 1; i < d; i++ {
		if !single {
			r = rand.Intn(2*B + 1)
			r = r - B
			random[i].SetInt(int64(r))
			random[i].Mod(&random[i], &settings.q)
		}
	}

	return random
}

// Generate d random big ints in [0, q).
func RqRandomQ(seed int64, d uint32, q bigint.Int) ([]bigint.Int, error) {
	random := make([]bigint.Int, d)
	BLen := (q.Value.BitLen() + 7) / 8

	var i uint32
	rand.Seed(seed)
	for i = 0; i < d; i++ {
		r := make([]byte, BLen)
		rLen, err := rand.Read(r)
		if rLen != BLen || err != nil {
			return nil, err
		}

		random[i].Value.SetBytes(r)
		random[i].Mod(&random[i], &q)
	}

	return random, nil
}

// convert v to LSB bits and set each bit in a ring
// Bits function in MatRiCT, return 64*1 matrix
func ConvertIntToRingBits(v uint64, d, precision uint32, q bigint.Int, nttParams *polynomial.NttParams) (*RingMartix, error) {
	// build a tmp ring
	r := new(ring.Ring)
	r.N = d
	r.Q = q
	r.Poly, _ = polynomial.NewPolynomial(d, q, nttParams)

	// build matrix
	bvec, err := NewRingMartix(precision, 1, nttParams)
	if bvec == nil {
		return nil, errors.New("NewRingMartix fail")
	}

	var bit uint64 = 1
	var i uint32
	coeffs := make([]bigint.Int, d)
	for i = 0; i < precision; i++ {
		if v&bit == bit {
			coeffs[0].SetInt(int64(1))
		} else {
			coeffs[0].SetInt(int64(0))
		}

		bit = bit << 1
		tmp, _ := ring.CopyRing(r)
		_ = tmp.Poly.SetCoefficients(coeffs)
		bvec.ringvectors[i].rings[0] = *tmp
	}

	return bvec, err
}

// convert v to LSB bits and pack each bit with CRT packing
func CRTPackInt(v uint64, d, precision uint32, q bigint.Int, nttParams *polynomial.NttParams) (*RingMartix, error) {
	// build a tmp ring
	r := new(ring.Ring)
	r.N = d
	r.Q = q
	r.Poly, _ = polynomial.NewPolynomial(d, q, nttParams)

	// build matrix
	bvec, err := NewRingMartix(1, 1, nttParams)
	if bvec == nil {
		return nil, errors.New("NewRingMartix fail")
	}

	var bit uint64 = 1
	delta := d / precision
	var i uint32
	coeffs := make([]bigint.Int, d)
	for i = 0; i < precision; i++ {
		if v&bit == bit {
			coeffs[i*delta].SetInt(int64(1))
		} else {
			coeffs[i*delta].SetInt(int64(0))
		}
		bit = bit << 1
	}

	tmp, _ := ring.CopyRing(r)
	_ = tmp.Poly.SetCoefficients(coeffs)
	bvec.ringvectors[0].rings[0] = *tmp

	return bvec, err
}

// build hat{1} = [1, 1, ..., 1]
func CRTPackOne(d, precision uint32, q bigint.Int, nttParams *polynomial.NttParams) (*RingMartix, error) {
	// build a tmp ring
	r := new(ring.Ring)
	r.N = d
	r.Q = q
	r.Poly, _ = polynomial.NewPolynomial(d, q, nttParams)

	// build matrix
	bvec, err := NewRingMartix(1, 1, nttParams)
	if bvec == nil {
		return nil, errors.New("NewRingMartix fail")
	}

	delta := d / precision
	var i uint32
	coeffs := make([]bigint.Int, d)
	for i = 0; i < precision; i++ {
		coeffs[i*delta].SetInt(int64(1))
	}

	tmp, _ := ring.CopyRing(r)
	_ = tmp.Poly.SetCoefficients(coeffs)
	bvec.ringvectors[0].rings[0] = *tmp

	return bvec, err
}

// show ring (test function)
func ShowRing(r *ring.Ring, coefflen uint32) {
	if settings.debug {
	}
	var i uint32
	coeffs := r.Poly.GetCoefficients()
	fmt.Printf("( ")
	for i = 0; i < settings.d && i < coefflen; i++ {
		fmt.Printf("%v ", coeffs[i].Value.Int64())
	}
	fmt.Printf(")\n")
}

func ShowRing_plus(r *ring.Ring, coefflen, precision uint32) {
	if settings.debug {
	}
	var i uint32
	delta := settings.d / precision
	coeffs := r.Poly.GetCoefficients()
	fmt.Printf("( ")
	for i = 0; i < settings.d && i < coefflen; i++ {
		if i%delta == 0 && i != 0 {
			fmt.Printf("\n  ")
		}
		fmt.Printf("%v ", coeffs[i].Value.Int64())
	}
	fmt.Printf(")\n")
}

// show ring vector (test function)
func ShowRingVector(r []ring.Ring, coefflen uint32) {
	var j uint32
	for i := range r {
		fmt.Printf("( ")
		coeffs := r[i].Poly.GetCoefficients()
		for j = 0; j < settings.d && j < coefflen; j++ {
			fmt.Printf("%v ", coeffs[j].Value.Int64())
		}
		fmt.Printf(")\n")
	}
}

// show matrix (test function)
func (m *RingMartix) ShowMatrix(coefflen uint32) {
	var i, j, k uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			if settings.d != 1 && coefflen != 1 {
				fmt.Printf("( ")
			}
			coeffs := m.ringvectors[i].rings[j].Poly.GetCoefficients()
			for k = 0; k < settings.d && k < coefflen; k++ {
				fmt.Printf("%v ", coeffs[k].Value.Int64())
			}
			if settings.d != 1 && coefflen != 1 {
				fmt.Printf(") ")
			}
		}
		fmt.Printf("\n")
	}
}

// set the rings in each matrix element
func (m *RingMartix) ToBytes() []byte {
	var b []byte
	var i, j, k uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			coeffs := m.ringvectors[i].rings[j].Poly.GetCoefficients()
			for k = 0; k < settings.d; k++ {
				if coeffs[k].Value.BitLen() == 0 {
					b = append(b, 0)
				} else {
					b = append(b, coeffs[k].Value.Bytes()...)
				}
			}
		}
	}

	return b
}

// set the rings in each matrix element
func (m *RingMartix) SetRingMartix(r *ring.Ring) *RingMartix {
	var i, j uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			tmp, _ := ring.CopyRing(r)
			m.ringvectors[i].rings[j] = *tmp
		}
	}

	return m
}

// set the matrix element to random coefficients in [-B, B]
func (m *RingMartix) SetRandomBRingMartix(r *ring.Ring, seed int64, d uint32, B int, single bool) *RingMartix {
	var i, j uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			tmp, _ := ring.CopyRing(r)
			coeffs := RqRandomB(seed, d, B, single)
			_ = tmp.Poly.SetCoefficients(coeffs)
			m.ringvectors[i].rings[j] = *tmp
			seed++ // seed should be reset more securely
		}
	}

	return m
}

// set the matrix element to random coefficients in [-B, B] for delta vector
// delta is a k * 1 sized vector
// a_0 = -sum_{i = 1}^{k - 1} a_i
func (m *RingMartix) SetRandomRingMartixForDelta(r *ring.Ring, seed int64, d uint32, B int) *RingMartix {
	var i uint32
	r0, _ := ring.CopyRing(r)
	zerocoeffs := make([]bigint.Int, d)
	_ = r0.Poly.SetCoefficients(zerocoeffs)

	for i = 1; i < m.col; i++ {
		tmp, _ := ring.CopyRing(r)
		coeffs := RqRandomB(seed, d, B, true)
		_ = tmp.Poly.SetCoefficients(coeffs)
		m.ringvectors[i].rings[0] = *tmp
		_, _ = r0.Sub(r0, tmp)
		seed++ // seed should be reset more securely
	}

	m.ringvectors[0].rings[0] = *r0
	return m
}

// set the  matrix element to random coefficients in [0, q)
func (m *RingMartix) SetRandomQRingMartix(r *ring.Ring, seed int64, d uint32, q bigint.Int) *RingMartix {
	var i, j uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			tmp, _ := ring.CopyRing(r)
			coeffs, _ := RqRandomQ(seed, d, q)
			_ = tmp.Poly.SetCoefficients(coeffs)
			m.ringvectors[i].rings[j] = *tmp
			seed++ // seed should be reset more securely
		}
	}

	return m
}

// set the  matrix element to zero
func (m *RingMartix) SetZeroRingMartix(r *ring.Ring, d uint32) *RingMartix {
	var i, j uint32
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			tmp, _ := ring.CopyRing(r)
			coeffs := make([]bigint.Int, d)
			_ = tmp.Poly.SetCoefficients(coeffs)
			m.ringvectors[i].rings[j] = *tmp
		}
	}

	return m
}

// copy matrix mat to m (only copy pointer)
func (m *RingMartix) CopyRingMartix(mat *RingMartix) *RingMartix {
	var i uint32
	for i = 0; i < mat.col; i++ {
		m.ringvectors[i].rings = mat.ringvectors[i].rings
	}

	m.col = mat.col
	m.row = mat.row
	return m
}
func (m *RingMartix) CopyLastRowMartix(mat *RingMartix) *RingMartix {
	m.ringvectors[0].rings = mat.ringvectors[mat.col-1].rings
	m.col = 1
	m.row = mat.row
	return m
}

func (m *RingMartix) CopyAllButLastRowMartix(mat *RingMartix) *RingMartix {
	var i uint32
	for i = 0; i < mat.col-1; i++ {
		m.ringvectors[i].rings = mat.ringvectors[i].rings
	}

	m.col = mat.col - 1
	m.row = mat.row
	return m
}

// combine two n*m and v*m matrix to one (n+v)*m matrix
func (m *RingMartix) RingMatCombine(m1, m2 *RingMartix) (*RingMartix, error) {
	if m1 == nil && m2 == nil {
		return nil, nil
	}

	var i uint32
	if m1 == nil || m1.col == 0 || m1.row == 0 {
		m.CopyRingMartix(m2)
		return m, nil
	} else if m2 == nil || m2.col == 0 || m2.row == 0 {
		m.CopyRingMartix(m1)
		return m, nil
	}

	if m1.row != m2.row {
		return nil, errors.New("matrix size not equal")
	}

	for i = 0; i < m1.col; i++ {
		m.ringvectors[i].rings = m1.ringvectors[i].rings
	}
	for i = 0; i < m2.col; i++ {
		m.ringvectors[i+m1.col].rings = m2.ringvectors[i].rings
	}

	m.col = m1.col + m2.col
	m.row = m2.row
	return m, nil
}

// check whether m equals n
func (m *RingMartix) RingMatIsEqual(n *RingMartix) bool {
	if m.row != n.row || m.col != n.col {
		return false
	}

	var i, j, k uint32
	d := m.ringvectors[i].rings[j].N
	for i = 0; i < m.col; i++ {
		for j = 0; j < m.row; j++ {
			mcoeffs := m.ringvectors[i].rings[j].GetCoefficients()
			ncoeffs := n.ringvectors[i].rings[j].GetCoefficients()
			for k = 0; k < d; k++ {
				if mcoeffs[k].Compare(&ncoeffs[k]) != 0 {
					return false
				}
			}
		}
	}

	return true
}

func (m *RingMartix) RingMatScalarAdd(r *ring.Ring, mat *RingMartix) (*RingMartix, error) {
	if mat.col == 0 || mat.row == 0 {
		return nil, errors.New("null matrix")
	}

	var err error
	var i, j uint32
	for i = 0; i < mat.col; i++ {
		for j = 0; j < mat.row; j++ {
			_, err = m.ringvectors[i].rings[j].Add(&mat.ringvectors[i].rings[j], r)
			err = nil
		}
	}

	m.col = mat.col
	m.row = mat.row
	return m, err
}

func (m *RingMartix) RingMatAdd(m1, m2 *RingMartix) (*RingMartix, error) {
	if m1.col == 0 || m1.row == 0 {
		return nil, errors.New("null matrix")
	}

	if m1.col != m2.col || m1.row != m2.row {
		return nil, errors.New("matrix size not equal")
	}

	var err error
	var i, j uint32
	for i = 0; i < m1.col; i++ {
		for j = 0; j < m1.row; j++ {
			_, err = m.ringvectors[i].rings[j].Add(&m1.ringvectors[i].rings[j], &m2.ringvectors[i].rings[j])
			//			_, err = m.ringvectors[i].rings[j].Mod(&m.ringvectors[i].rings[j], settings.q)
		}
	}

	m.col = m1.col
	m.row = m2.row
	return m, err
}

func (m *RingMartix) RingMatSub(m1, m2 *RingMartix) (*RingMartix, error) {
	if m1.col == 0 || m1.row == 0 {
		return nil, errors.New("null matrix")
	}

	if m1.col != m2.col || m1.row != m2.row {
		return nil, errors.New("matrix size not equal")
	}

	var err error
	var i, j uint32
	for i = 0; i < m1.col; i++ {
		for j = 0; j < m1.row; j++ {
			_, err = m.ringvectors[i].rings[j].Sub(&m1.ringvectors[i].rings[j], &m2.ringvectors[i].rings[j])
			_, err = m.ringvectors[i].rings[j].Mod(&m.ringvectors[i].rings[j], settings.q)
		}
	}

	m.col = m1.col
	m.row = m2.row
	return m, err
}

func (m *RingMartix) RingMatScalarMul(r *ring.Ring, mat *RingMartix) (*RingMartix, error) {
	if mat.col == 0 || mat.row == 0 {
		return nil, errors.New("null matrix")
	}

	var err error
	var i, j uint32
	for i = 0; i < mat.col; i++ {
		for j = 0; j < mat.row; j++ {
			_, err = m.ringvectors[i].rings[j].MulPoly(&mat.ringvectors[i].rings[j], r)
			_, err = m.ringvectors[i].rings[j].Mod(&m.ringvectors[i].rings[j], settings.q)
			err = nil
		}
	}

	m.col = mat.col
	m.row = mat.row
	return m, err
}

func (m *RingMartix) RingMatMul(m1, m2 *RingMartix) (*RingMartix, error) {
	if m1.col == 0 || m1.row == 0 {
		return nil, errors.New("null matrix")
	}

	if m1.row != m2.col {
		return nil, errors.New("matrix size not multipliable")
	}
	zero := make([]bigint.Int, settings.d)

	var err error
	var i, j, k uint32
	for i = 0; i < m1.col; i++ {
		for j = 0; j < m2.row; j++ {
			sum, _ := ring.CopyRing(&(m.ringvectors[i].rings[j]))
			_ = sum.Poly.SetCoefficients(zero)

			for k = 0; k < m1.row; k++ {
				tmp, _ := ring.CopyRing(&(m.ringvectors[i].rings[j]))
				_ = tmp.Poly.SetCoefficients(zero)
				// there is a bug in MulPoly function to handle same inputs
				if MulPolyBug && m1 == m2 {
					m1tmp, _ := ring.CopyRing(&m1.ringvectors[i].rings[k])
					_ = m1tmp.Poly.SetCoefficients(m1.ringvectors[i].rings[j].Poly.GetCoefficients())
					_, err = tmp.MulPoly(m1tmp, &m2.ringvectors[k].rings[j])
				} else {
					_, err = tmp.MulPoly(&m1.ringvectors[i].rings[k], &m2.ringvectors[k].rings[j])
				}
				_, err = sum.Add(sum, tmp)
			}

			_ = m.ringvectors[i].rings[j].Poly.SetCoefficients(sum.GetCoefficients())
		}
	}

	m.col = m1.col
	m.row = m2.row
	return m, err
}

// m(i, j) = m1(i, j) * m2(i, j)
func (m *RingMartix) RingMatHadamardProd(m1, m2 *RingMartix) (*RingMartix, error) {
	if m1.col != m2.col || m1.row != m2.row {
		return nil, errors.New("matrix size not multipliable")
	}

	if m1.col == 0 || m1.row == 0 {
		return nil, errors.New("null matrix")
	}

	var err error
	var i, j uint32
	for i = 0; i < m1.col; i++ {
		for j = 0; j < m1.row; j++ {
			// there is a bug in MulPoly function to handle same inputs
			if MulPolyBug && m1 == m2 {
				tmp, _ := ring.CopyRing(&m1.ringvectors[i].rings[j])
				_ = tmp.Poly.SetCoefficients(m1.ringvectors[i].rings[j].Poly.GetCoefficients())
				_, err = m.ringvectors[i].rings[j].MulPoly(tmp, &m2.ringvectors[i].rings[j])
			} else {
				_, err = m.ringvectors[i].rings[j].MulPoly(&m1.ringvectors[i].rings[j], &m2.ringvectors[i].rings[j])
			}
		}
	}

	m.col = m1.col
	m.row = m1.row
	return m, err
}
