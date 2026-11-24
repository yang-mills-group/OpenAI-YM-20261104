import YM.RGComparison.Core16.Silk.Net
/-!
# Joint estimates on Θ-rank Gardner kernels. Matter:Hess outward and still relative
Use for orientation cross & stencil delivery, post-p theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D L I J: Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L][Fintype I]
variable {X:Shelf G A D} (P:Planet X S ι k T) {p:Stuff G ι L} {q:Stuff G ι I} {ψ:(L→ G.Color)→ℝ} {φ:(I→G.Color)→ℝ}

def owner (p:Stuff G ι L) (ψ:(L→ G.Color)→ℝ) (R:Rail G ι→Roll):= day (night p ψ R []) 0

def stamps (p:Stuff G ι L)(ψ:(L→ G.Color)→ℝ) := day (night p ψ (price P) []) 0
lemma booked {f:Melody G ι}{N:ℕ}{c:ℝ}(H:P.Steady)(he: Visible X ψ f p N c)(h: ContDiffAt ℝ ∞ ψ 0) : train (fun g=>P.expect g (f g)) (stamps P p ψ) :=by
    apply (prelude (P:=P) [] H he h).travel -- arg P implicit
    apply Eventually.of_forall; intro i; unfold sight; rw [show sing (G:=G) (ι:=ι) [] _=1 from rfl,one_mul]

def joining (p: Stuff G ι L)(q:Stuff G ι I)(ψ:(L→G.Color)→ℝ)(φ:(I→G.Color)→ℝ):= stamps P (woven p q) (unite ψ φ)-stamps P p ψ*stamps P q φ

variable {P}(H:P.Steady){ℓ: Finset ι} {C:ℝ}{n b:ℕ}

omit [Fintype ι] in
lemma owner_sub (p:Stuff G ι L)(ψ :(L→G.Color)→ℝ) (R U : Rail G ι→Roll): owner p ψ (R-U)=owner p ψ R-owner p ψ U:=by unfold owner; rw [show night p ψ (R-U) []= fun i=> night p ψ R [] i - night p ψ U [] i from funext fun i=>night_sub ..]; exact day_sub ..
omit [Fintype ι] in
lemma owner_cost (he:0≤C){U:Rail G ι→Roll}{B:ℝ}(h:0≤B)(hx:celery p ℓ B)(hn:n≤b)
    (hy: ∀ i≤b,∀ j, j≤b→ ∀ f:Wires G L i,|nth j (U (weave p f))| ≤ C) : |nth n (owner p ψ U)| ≤ C * lint ψ 0 b B := by
    unfold owner; rw [show night p ψ U []= fun i=> night p ψ U [] (0+i) from funext fun i=> by rw [zero_add]]; refine silk_price he h hx hn ?_; intro i hi f; rw [List.append_nil]; exact hy _ (by omega) _ (by omega) f

include H
lemma partner (he:ContDiffAt ℝ ω ψ 0)(hx:ContDiffAt ℝ ω φ 0): joining P p q ψ φ = day (fun j => ∑ k∈antidiagonal j,twin p q ψ φ (gap P) k.1 k.2) 0:=by
    let f:= night p ψ (price P) []; let g:= night q φ (price P) []; have h (j k:ℕ): twin p q ψ φ (gap P) j k = joins P p q ψ φ j k-f j*g k := by
       let u (w:Rail G ι):= night p ψ (fun y=> price P (y++w)) [] j; let v w:= f j*price P w
       have h (w: Rail G ι):night p ψ (gap P w) [] j=u w-v w := by rw [show gap P w= (fun y=> price P (y++w))-(fun y=> price P y*price P w) from rfl,night_sub,night_mul]
       unfold twin; simp_rw [h]; change night q φ (u-v) [] k=_; rw [night_sub]; congr 1
       unfold v; simp_rw [mul_comm (f j),night_mul]; rfl
    unfold joining stamps; rw [←subday,← day_sub]; unfold morning; simp_rw [h,sum_sub_distrib]; congr 1; funext i; rw [join_bill (p:=p) (q:=q) P he hx H]
section ethos
variable {u v : Finset ι}{N j i l:ℕ} (p' : celery p u X.Q) (q' : celery q v X.Q) (hψ:ContDiffAt ℝ ω ψ 0)(hφ:ContDiffAt ℝ ω φ 0) (hpos:0≤ C)(hx:Past X C n n n)(hw:∀ i∈u,∀ j∈v,N≤ separation (P.loc i) (P.loc j))


include p' q' hpos hx hw
private lemma touch (hj:j≤n)(hi:i≤n)(hl:l≤n): |nth j (twin p q ψ φ (gap P) i l)| ≤ (((C / costLamp X N)*presence ψ X.Q i)*presence φ X.Q l):=by
    have he:0≤C/costLamp X N:=div_nonneg hpos coin_pos.le
    have h:=H.prices.thick.1.le
    apply sight_cost _ h q'
    · intro a; apply sight_cost (ψ:=ψ) he h p'; intro b; rw [List.append_nil,List.append_nil]
      refine hx _ _ _ _ _ _ S P H j hj _ ((length_bound q a).trans hl) _ ((length_bound p b).trans hi) N ?_
      intro i hi j hj; rw [separation_comm]; exact hw j.1 (rails p b p' j hj) i.1 (rails q a q' i hi) -- h_unused rename
    exact mul_nonneg he (by unfold presence; positivity)

include hψ hφ
def bond_fee (ψ:(L→ G.Color)→ℝ) (φ:(I→ G.Color)→ℝ) (B:ℝ)(k:ℕ): ℝ:= ∑ i∈range (k+1),∑ j∈antidiagonal i,presence ψ B j.1 *presence φ B j.2
lemma ramp (hi:i≤n): |nth i (joining P p q ψ φ)| ≤ C/costLamp X N* bond_fee ψ φ X.Q n:=by
    rw [partner H hψ hφ]; unfold bond_fee; rw [mul_sum]; let b i:=∑ j∈antidiagonal i,presence ψ X.Q j.1*presence φ X.Q j.2; let x:=C/costLamp X N; have hb(i):0≤b i:=by have h:= H.prices.thick.1; unfold b presence; positivity
    have hx₀:0≤x:=div_nonneg hpos coin_pos.le
    refine day_rate (F:=fun i=>x*b i) (fun i hi=> mul_nonneg hx₀ (hb i)) hi (fun y hy=> ?_); unfold nth b; rw [map_sum,mul_sum]; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j hj=>?_); have he:=Finset.mem_antidiagonal.mp hj; exact (touch H p' q' hpos hx hw (tsub_le_self.trans hi) (by omega) (by omega)).trans_eq (by ring)
end ethos
end YM.RGComparison.Core16.Silk
