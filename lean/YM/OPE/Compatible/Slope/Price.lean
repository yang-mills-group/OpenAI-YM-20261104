import YM.OPE.Compatible.Slope.Feast
/-!
# Graded moments in both sockets
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I : Type*} {r k j n d m:ℕ}{x U V:ℝ}{P:Flight j k}
def Charm (I:Type*)(d:ℕ):Submodule ℝ (Lieu I→ℝ):= Submodule.span ℝ {f | ∃ l:List I,l.length=d ∧ f=tasting l}
lemma charm_flavor (i:ℕ): Charm I i ≤ Flavor I i:=by
   apply Submodule.span_mono; rintro v ⟨l,h,hx⟩; exact ⟨l,h.le,hx⟩
lemma charms (l:List I): tasting l∈ Charm I l.length:= Submodule.subset_span ⟨l,rfl,rfl⟩
lemma position_charm (x:I) : (fun p:Lieu I=> p x)∈Charm I 1:=by convert! charms [x];simp [tasting]
private lemma chop {f:Lieu I→ℝ}(h:f∈ Charm I d)(P:(Lieu I→ℝ)→Prop) (hp:∀ l:List I, l.length=d→ P (tasting l))(hz:P 0)(hd:∀ v w,v∈Charm I d→w∈Charm I d→ P v→ P w→ P (v+w))(hs:∀ (r:ℝ) v,v∈Charm I d→P v→ P (r•v)): P f:=by
   refine Submodule.span_induction (p:=fun v _=>P v) ?_ hz hd hs h; rintro x ⟨l,hl,hx⟩; rw [hx]; exact hp _ hl
lemma charm_prod {m n:ℕ}{f g:Lieu I→ℝ}(h:f∈ Charm I m)(hp:g∈Charm I n): f*g ∈ Charm I (m+n):=by
   let U:=Charm I (m+n)
   refine chop h (fun f=> f*g∈U) (fun i hi=>?_) (by rw [zero_mul]; exact U.zero_mem) (fun v w _ _ hv hw=>?_) (fun v w _ hw=>?_)
   · refine chop hp (fun g=> tasting i*g∈U) ?_ ?_ ?_ ?_
     · intro j hj; rw [show tasting i*tasting j=tasting (i++j) from funext fun x=>by simp [tasting]]; simpa only [List.length_append,hi,hj] using! charms (i++j)
     · rw [mul_zero];exact U.zero_mem
     · intro v w _ _ a b; rw [mul_add]; exact U.add_mem a b
     intro v w _ a; rw [mul_smul_comm]; exact U.smul_mem _ a
   · rw [add_mul]; exact U.add_mem hv hw
   rw [smul_mul_assoc]; exact U.smul_mem _ hw
-- representation of settlement
abbrev fall (x:Lieu (Keys (r+1))) : Lieu (Keys r):= fun j=> x (j.1.succ,j.2)-x (0,j.2)
lemma fall_charm (l:List (Keys r)): tasting l ∘ fall∈Charm (Keys (r+1)) l.length:=by
   induction l with
   | nil=> exact charms ([] : List (Keys (r+1)))
   | cons i l h=>
      let u x:=fall x i
      have hh: u ∈ Charm (Keys (r+1)) 1:= (Charm _ _).sub_mem (position_charm (i.1.succ,i.2)) (position_charm (0,i.2))
      rw [List.length_cons,add_comm l.length 1]; exact charm_prod hh h
private lemma fall_wreath_translit (z : Cover) (y : Bin r) :
    fall (translit (wreath r (z,y))) = translit y := by
  funext ⟨i,j⟩
  change (↑(stepOut (wreath r (z,y)) i.succ j) : ℝ) - (↑(stepOut (wreath r (z,y)) 0 j) : ℝ) = _
  rw [flowPart, header, Pi.add_apply]
  push_cast
  change _ = (↑(stepOut y i j) : ℝ)
  ring

private lemma midland_well_sum (q : Bin (r+1) → ℝ) (v : Lieu (Keys r) → ℝ) :
    well (midland q) v = ∑' y : Bin r, ∑' z : Cover, q (wreath r (z,y)) * v (translit y) := by
  unfold well midland
  exact tsum_congr (fun y => (tsum_mul_right).symm)

private lemma transfer_sum {A B C : Type*} (e : A × B ≃ C) (q v : C → ℝ) (u : B → ℝ)
    (hv : ∀ z y, v (e (z,y)) = u y) (hs : Summable (fun i => q i * v i)) :
    (∑' y : B, ∑' z : A, q (e (z,y)) * u y) = ∑' i : C, q i * v i := by
  let f (z : A) (y : B) := q (e (z,y)) * v (e (z,y))
  have hf : Summable (uncurry f) := e.summable_iff.mpr hs
  calc
    _ = ∑' y : B, ∑' z : A, f z y :=
      tsum_congr (fun y => tsum_congr (fun z => congrArg (q (e (z,y)) * ·) (hv z y).symm))
    _ = ∑' z : A, ∑' y : B, f z y := hf.tsum_comm
    _ = _ := hf.tsum_prod.symm.trans (e.tsum_eq (fun i => q i * v i))

lemma mid_price {q:Bin (r+1)→ℝ} (h:Sack (poise m) q U)(l:List (Keys r))(he:l.length≤m): well (midland q) (tasting l)=well q (tasting l ∘ fall):=by
  have hv : tasting l ∘ fall ∈ Flavor (Keys (r+1)) m :=
    flavor_up he (charm_flavor (I:=Keys (r+1)) l.length (fall_charm l))
  rw [midland_well_sum]
  exact transfer_sum (wreath r) q ((tasting l ∘ fall) ∘ translit) (tasting l ∘ translit)
    (fun z y => congrArg (tasting l) (fall_wreath_translit z y)) (gardens hv h)
lemma well_plus [Fintype I]{p:Shift I→ℝ}{f g:Lieu I→ℝ}(hf:f∈Flavor I m)(hg:g∈Flavor I m)(h:Sack (poise m) p U): well p (f+g)= well p f+well p g:=by
    unfold well; simp_rw [Pi.add_apply,mul_add]; exact Summable.tsum_add (gardens hf h) (gardens hg h)
lemma well_scale [Fintype I] (p:Shift I→ℝ)(g:Lieu I→ℝ)(v:ℝ): well p (v • g)=v*well p g:=by
    unfold well; simp_rw [Pi.smul_apply,smul_eq_mul, mul_left_comm (p _) v,tsum_mul_left]
lemma grab_rank [Fintype I] {p q:Shift I→ℝ} (he:d≤m) (h : Sack (poise m) p U)(g:Sack (poise m) q V){x:ℝ}(hk:∀ l:List I, l.length=d→ well p (tasting l)=x*well q (tasting l)){r:Lieu I→ℝ}(hr:r∈Charm I d): well p r=x*well q r:=by
    apply chop hr (fun r=> well p r=x*well q r) hk
    · simp [well]
    · intro i j hi hj H G; rw [well_plus (flavor_up he (charm_flavor _ hi)) (flavor_up he (charm_flavor _ hj)) h,H,G,well_plus (flavor_up he (charm_flavor _ hi)) (flavor_up he (charm_flavor _ hj)) g,mul_add]
    intro r f _ H; rw [well_scale,well_scale,H]; ring
lemma upright (p:Bin r→ℝ)(z): midland (upland p) z=p z:=by
   unfold midland upland; rw [tsum_eq_single 0]; simp [header,flattenZ]
   intro x hx; simp [header,hx]
end YM.OPE.Flume
