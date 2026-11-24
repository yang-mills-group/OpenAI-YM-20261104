import YM.SchemeRG11.Sew.Frost
/-! Uniform pricing services for face-centroid.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical Pointwise
variable {I J:Type*}{G: Gauge} {T:Align.Itinerary}
local notation "D₁" => Atoll.land G
def spanX {K:Type*}(s:Finset I)(L:I→J→ K→ Touch G): Set (J→Touch G):={v|∃a∈s,∃ u:K,v=fun j=>L a j u} -- K binder
abbrev Crawl:= ℕ × Cover
def Worth (S:ℕ → Cover→Prop)(p:Crawl→ℝ):Prop:=∃ C>0,∀ᶠ i in atTop,∀x,S i x→|p (i,x)| ≤ C
def Funds(S:ℕ → Cover→ Prop):Subalgebra ℝ (Crawl→ℝ) where
 carrier:= {f|Worth S f}
 algebraMap_mem' k:= ⟨|k| +1, by positivity,Eventually.of_forall fun x y h=>by change |k|≤ _; linarith⟩
 zero_mem' := ⟨1,zero_lt_one,Eventually.of_forall fun x y _=>by simp⟩
 one_mem':=⟨1,zero_lt_one,Eventually.of_forall fun x y _=>by simp⟩
 add_mem':=by
    rintro a b ⟨C,hC,H⟩ ⟨D,hD,E⟩; refine ⟨C+D,by positivity,(H.and E).mono ?_⟩; exact fun i h p ht=> (abs_add_le ..).trans (add_le_add (h.1 _ ht) (h.2 _ ht))
 mul_mem':=by
    rintro a b ⟨C,hC,H⟩ ⟨D,hD,E⟩; refine ⟨C*D,by positivity,(H.and E).mono ?_⟩; intro i h p ht; rw [Pi.mul_apply,abs_mul]; exact mul_le_mul (h.1 p ht) (h.2 p ht) (abs_nonneg _) hC.le -- correct second
-- dress rows with lifted n(T)
variable (s:Finset I)(T)
def cords(v:I→ ℕ → Cover)(i:I)(k:Crawl)(q:Key G):Touch G:= lensLeg T q (v i) k.1
def hops(S:ℕ→ Cover→Prop)(r:ℝ)(z v:Crawl → Cover):Prop:= ∀ᶠ i in atTop,∀ x,S i x→ r≤baseU T i (z (i,x)-v (i,x))
variable {T}
lemma spending {r:ℝ}(hr:r>0){S}{z v:Crawl → Cover}(V:ℕ → Cover)(h:∀x:Crawl,v x=V x.1) (hp:hops T S r z v)(ρ:Crawl→ℝ){m:ℕ}{a:Touch G}(ha:a∈Stepper G m)(b:Key G)(he:∃ C>0,∀ᶠ i in atTop,∀x,S i x→|ρ (i,x)| ≤ C * baseU T i (z (i,x)-v (i,x)) ^ 2):
 (fun x:Crawl=>(D₁).bed ((ρ x*T.gap x.1 ^ (-(m+1:ℤ))) • flex (z x) a) (lensLeg T b V x.1)) ∈ Funds S:=by
 obtain ⟨C,hC,H⟩:=he; obtain ⟨P,hP,Q⟩:= fueled (T:=T) ha (high_probe b) hr
 let n:ℤ:= m+1+(((b.1+1:ℕ):ℤ)+1)
 refine ⟨C*r^(2-n)*P, mul_pos (mul_pos hC (zpow_pos hr _)) hP,(H.and (Q.and hp)).mono ?_⟩
 intro i W t e; let x:Crawl:=(i,t); let D:= baseU T i (z x-v x)
 have he:r≤ D:= W.2.2 _ e
 let V1:= T.gap i^(-(m+1:ℤ)-(((b.1+1:ℕ):ℤ)+1))*(D₁).bed (flex (z x-v x) a) (leafProbe 1 b)
 change |(D₁).bed _ (lensLeg _ _ _ _)| ≤ _; have hv:T.gap i>0:=T.positive _
 have Hz : (D₁).bed ((ρ x*T.gap x.1 ^ (-(m+1:ℤ))) • flex (z x) a) (lensLeg T b V x.1)=ρ x* V1:=by rw [paid_s,lens_l, liftC, double_comm, paid_s,double_comm, commons]; unfold V1; rw [h x,zpow_sub₀ hv.ne',zpow_neg (T.gap i) ((m:ℤ)+1),zpow_neg]; ring -- fragile
 rw [Hz,abs_mul]
 have hv := W.2.1 (z x-v x) he
 have hD : D>0:= hr.trans_le he
 have hZ:r^(2-n)*D^n ≥ D^2:=by
    have hr':0≤ n-2:=by unfold n; omega
    have H:=zpow_le_zpow_left₀ hr' hr.le he; rw [zpow_sub₀ hr.ne',zpow_sub₀ hD.ne'] at H
    rw [zpow_sub₀ hr.ne',zpow_two]; rw [zpow_two,zpow_two] at H; field_simp at H ⊢ -- too much
    linarith only [H]
 calc |ρ x| * |V1| ≤ (C * D^2)*|V1| := mul_le_mul_of_nonneg_right (W.1 _ e) (abs_nonneg _)
      _ ≤ C*(r^(2-n)*D^n)*|V1|:=by gcongr
      _ = C*r^(2-n)*(|V1| * D^n):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hv (mul_nonneg hC.le (zpow_pos hr _).le)
variable {S:ℕ → Cover→Prop}
lemma earned {f:ℕ→ℝ}(h:Finishes f): Worth S (fun i=> f i.1):=by
 have ht:= (h.choose_spec.norm).eventually (gt_mem_nhds (lt_add_one ‖h.choose‖)); exact ⟨‖h.choose‖+1,by positivity,ht.mono fun i hi j h=>hi.le⟩
lemma chair (v:I→ℕ → Cover)(L: Finset I)(y:I→ E4) (h:∀i∈L,Along T (v i) (y i))(hp:∀i∈L,∀j∈L,i≠ j → y i≠y j): priceS (D₁) (cords T v) (Funds S) L:=by intro i hi j hj h' a b; exact earned (f:=fun x=> (D₁).bed _ _) (reachPrice L _ _ h hp i hi j hj h' a b) -- cost point
end YM.SchemeRG11.Sew
