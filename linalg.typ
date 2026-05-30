#import "@preview/peano": q, surd

#let surd-from-rat = surd.from-rat
#let surd-from-quadratic = surd.from-quadratic
#let surd-from-cubic = surd.from-cubic
#let surd-to-float = surd.to-float

#let is-mat(m) = type(m) == array and m.len() > 0 and type(m.at(0)) == array
#let transpose(m) = range(0, m.at(0).len()).map(c => range(0, m.len()).map(r => m.at(r).at(c)))

#let rq-op(m, f) = m.map(row => row.map(f))
#let rq-add(a, b) = a.zip(b).map(((x, y)) => x.zip(y).map(((u, v)) => q.add(u, v)))
#let rq-scale(s, m) = rq-op(m, x => q.mul(s, x))
#let rq-identity(n) = range(n).map(i => range(n).map(j => if i == j { q.from(1) } else { q.from(0) }))

#let rq-dot(a, b) = a.zip(b).map(((x, y)) => q.mul(x, y)).fold(q.from(0), q.add)

#let rq-matmul(a, b) = {
  let bt = transpose(b)
  a.map(row => bt.map(col => rq-dot(row, col)))
}

#let rq-trace(m) = m.enumerate().map(((i, row)) => row.at(i)).fold(q.from(0), q.add)

#let rq-det(m) = {
  let n = m.len()
  if n == 0 { panic("empty matrix") }
  if n == 1 { return m.at(0).at(0) }
  if n == 2 {
    return q.sub(q.mul(m.at(0).at(0), m.at(1).at(1)), q.mul(m.at(1).at(0), m.at(0).at(1)))
  }
  let a = m.map(row => row)
  let sign = 1
  let prev = q.from(1)
  for i in range(n - 1) {
    if q.eq(a.at(i).at(i), 0) {
      let swap-found = false
      for j in range(i + 1, n) {
        if not q.eq(a.at(j).at(i), 0) {
          (a.at(i), a.at(j)) = (a.at(j), a.at(i))
          sign = -sign
          swap-found = true
          break
        }
      }
      if not swap-found { return q.from(0) }
    }
    for j in range(i + 1, n) {
      for k in range(i + 1, n) {
        let num = q.sub(q.mul(a.at(i).at(i), a.at(j).at(k)), q.mul(a.at(j).at(i), a.at(i).at(k)))
        a.at(j).at(k) = q.div(num, prev)
      }
    }
    prev = a.at(i).at(i)
  }
  let d = range(n).fold(q.from(sign), (acc, i) => q.mul(acc, a.at(i).at(i)))
  d
}

#let rq-char-poly(m) = {
  let n = m.len()
  range(1, n + 1).fold(
    (b: rq-identity(n), ps: ()),
    (acc, k) => {
      let pk = q.div(q.neg(rq-trace(rq-matmul(m, acc.b))), k)
      (
        b: rq-add(rq-matmul(m, acc.b), rq-scale(pk, rq-identity(n))),
        ps: acc.ps + (pk,),
      )
    },
  ).ps
}

#let eig-vals(m) = {
  assert(is-mat(m), message: "eig-vals expects a matrix")
  let n = m.len()
  assert(m.at(0).len() == n, message: "eig-vals expects a square matrix")
  let ps = rq-char-poly(m)
  if n == 1 {
    let v = (surd-from-rat)(m.at(0).at(0))
    (v,)
  } else if n == 2 {
    (surd-from-quadratic)(q.neg(ps.at(0)), ps.at(1))
  } else if n == 3 {
    (surd-from-cubic)(ps.at(0), ps.at(1), ps.at(2))
  } else {
    panic("eig-vals supports matrices up to 3×3")
  }
}

#let eig-vecs-sym(m, vals) = {
  let n = m.len()
  if n == 1 {
    ((q.from(1),),)
  } else if n == 2 {
    let a = m.at(0).at(0)
    let b = m.at(0).at(1)
    let d = m.at(1).at(1)
    vals.map(lam => {
      let lf = (surd-to-float)(lam)
      let af = q.to-float(a)
      let bf = q.to-float(b)
      let df = q.to-float(d)
      if calc.abs(bf) > 1e-12 {
        (bf, lf - af)
      } else if calc.abs(lf - af) < calc.abs(lf - df) {
        (1.0, 0.0)
      } else {
        (0.0, 1.0)
      }
    })
  } else {
    panic("eig-vecs-sym supports matrices up to 2×2")
  }
}

#let psd(a, b, d) = ((q.from(a), q.from(b)), (q.from(b), q.from(d)))
