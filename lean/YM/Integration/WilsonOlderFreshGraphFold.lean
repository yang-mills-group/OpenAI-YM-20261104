import YM.Integration.WilsonOlderFreshGraphRoster

/-! The real source table of the rooted ink field is the prescribed folded
finite polynomial, pointwise on every auxiliary side and test. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphFold
open Function Filter Finset Lattice Laurent RG FormalBulk08 Reef Lava Lotus Shore Mesa Gorge Rift Kemp
open QuadraticLocal QuadraticLocal.Sunrise Push.AbsoluteSums AllOrder.Ink Primitives.TwoWave
open WilsonOlderFreshGraphInk
open scoped Topology ENNReal BigOperators Classical

theorem fold {ι₀:Type} [Fintype ι₀] {r:ℕ} (T:Tile (Biglot ι₀) r) (hs:Summable T)
    (n:Side) (L:chain (Tor n ι₀) r→ℝ):
    (∑' z:chain (Biglot ι₀) r,T z * L (Lotus.drip n ∘ z)) =
      ∑ q:chain (Tor n ι₀) r, sieve n T q * L q := by
  let X (q:chain (Tor n ι₀) r)(v:chain (Biglot ι₀) r):ℝ:=
    (if Lotus.drip n ∘ v=q then T v else 0)*L q
  have recovers (v:chain (Biglot ι₀) r):
      (∑q,X q v) = T v*L (Lotus.drip n ∘ v) := by classical simp [X,ite_mul]
  have price (q):Summable (X q) := by
    have hx:=hs.indicator {v|Lotus.drip n ∘ v=q}
    exact (hx.mul_right (L q)).congr (fun v=>by simp [X,Set.indicator_apply])
  calc
    _=∑'v,∑q,X q v :=tsum_congr fun v=>(recovers v).symm
    _=∑q,∑'v,X q v := Summable.tsum_finsetSum (fun q _=>price q)
    _=_:=by
      apply Finset.sum_congr rfl
      intro q _
      rw [sieve_i,←tsum_mul_right]

theorem filed {ι₀:Type} [Fintype ι₀] {r:ℕ} (T:Tile (Biglot ι₀) r) (hs:Summable T)
    (n:Side) (y:Site n) (A:Board ι₀ n ℝ) (x:Board Unit n ℝ):
    (tensor T).site n y (mingle A x) =
      x (y,())*MvPolynomial.eval (fun u:Tor n ι₀=>A (y+u.1,u.2)) (facade r (sieve n T)) := by
  rw [WilsonOlderFreshGraphInk.site]
  congr 1
  let point (q:chain (Tor n ι₀) r):= ∏i,A (y+(q i).1,(q i).2)
  calc
    _ = ∑q,sieve n T q * point q := fold T hs n point
    _ = _ := by simp [facade,Lava.cards,point]

theorem whole {ι₀:Type} [Fintype ι₀] {r:ℕ} (T:Tile (Biglot ι₀) r) (hs:Summable T)
    (n:Side) (A:Board ι₀ n ℝ) (x:Board Unit n ℝ):
    (tensor T).table n (mingle A x) = ∑y:Site n,
      x (y,())*MvPolynomial.eval (fun u:Tor n ι₀=>A (y+u.1,u.2)) (facade r (sieve n T)) :=
  by rw [Field.table_apply];exact Finset.sum_congr rfl fun y _=>filed T hs n y A x

end YM.Integration.WilsonOlderFreshGraphFold
end
