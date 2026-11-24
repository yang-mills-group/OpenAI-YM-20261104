import YM.LocalTaylorR2.Edition
/-!
# Priced local Taylor letters (all addresses)

A contaminated molecule already costs all powers at the very same output
threshold/locality, not smuggling a shorter-support representation into a
hit test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves RG01.Survive PhysicalNext.Repeat
open Charge Candle Tender
namespace Price
variable {j k n l : ℕ} {v r d A a x B D C' ζ η θ c' q w ρ: ℝ} {χ : Chi}
variable (N:Captain H j C' d v w A a r B q (n+j) χ)
set_option quotPrecheck false
local notation "Ξ" => N.conduit
variable (hB: LocalBookingsR2 ζ c' N.conduit) (M:StoresR2 H j v d A D k x n χ)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hp:1≤ρ)
    (hθ:1≤θ) (he:Charge.Allows l j θ)
variable (hs:ρ*c'≤1) (hr: ρ^(l+1) ≤ betaF G s L^ζ) (hh:betaF G s L^ζ ≤ Real.exp (Q.costs L μ R.beta s C').markSeed)

def tubeRate (x D r:ℝ) (l j:ℕ) := x*(1+D+2*r*(l+3:ℝ))^j
def fare (N:Captain H j C' d v w A a r B q (n+j) χ) (x D θ:ℝ) (U : Molecule S) (p:Paint U l):= forge N.conduit θ p*tubeRate x D r l j*(1+H.shapeW U)^(n+j)
def schemePrice (D x θ:ℝ) (i : H.ThinP) (p:Orders l):ℝ:=if live H i then convolve p (fare N x D θ i.val) else if p=perch l ∧ vetted H i then B* (Ξ).meant i.val (n+j) else 0
include M hθ
lemma baseN {U} (p:Paint U l):0≤fare N x D θ U p := by
  unfold fare tubeRate; have hp := M.sure; have hr:= (Ξ).active; have hx := H.positive_volume U; have he:= forgeN (Ξ) hθ p; have hz:= M.fuel; positivity
lemma positional (i:H.ThinP)(p:Orders l): 0 ≤ schemePrice N D x θ i p:=by
  unfold schemePrice; split
  · exact Finset.sum_nonneg fun _ _=> baseN N M hθ _
  split
  · exact mul_nonneg N.balance ((Ξ).meant_nonneg ..)
  exact le_rfl

include hB h hζ hp he hs
lemma muster (i:H.ThinP) (p:Orders l) (V:Config G c) (hv:Healthy (Pressure.temp s) (H.smallAt i) V): Ore V (sprig H χ i p) v (schemePrice N D x θ i p) j:= by
  unfold schemePrice; split
  next hf=>
    have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hB.leases.hit 0)) hp).trans hs
    have hh(p':Paint i.val l): Ore V (episode H χ i.val (letters H p')) v (fare N x D θ i.val p') j:= by
      have hb:0≤2*r*(l+3:ℝ):=by have hq:=(Ξ).active; positivity
      have hw:= holds M _ (forgeN (Ξ) hθ p') hb _ (sumSpeed (U':=i.val) hB p' (Subset.refl _) hf.1.2 he (slack _ hB h hζ ht))
      exact episodeCost H N.oboe i.2.2 (letterSect H _ _ (Subset.refl _)) hw V hv
    intro E _ _ _ U x hz hV; apply Brush.shimmy _ (realized H χ i N.oboe hf p E U x hV (hz.symm ▸ hv))
    unfold Candle.script; simp_rw [if_pos hf]; exact Brush.spree _ (fun p' v=> episode H χ i.val (letters H p') (U v)) _ zero_le_one fun i _=> hh i E U x hz hV
  next hf=> split
            next hU=> rw [identity_zero H χ i hf hU.1]; exact (N.collective i V).2 hv
            next hh=> rw [show sprig H χ i p=(fun _=>0) from by
                        by_cases hv:vetted H i
                        · exact quiet H χ i hf fun hx=> hh ⟨hx,hv⟩
                        exact dormant H χ i hv p]
                      intro E _ _ _ U x h hp; exact (Brush.certified zero_le_one 0).climb (norm_zero.le) le_rfl
-- contaminated if not live (structural invalid has identically zero prices).
-- account
local notation "K"=> ((l+1:ℝ)*θ*ρ)
abbrev slope (D x B r : ℝ) (l j : ℕ) := B+tubeRate x D r l j
def result (θ ζ ρ D x:ℝ) (l:ℕ) (i:H.ThinP):ℝ:= slope D x B r l j * advantage (Ξ) ((l+1:ℝ)*θ*ρ) ζ (n+j) i.val
omit hB he hs in
lemma tall (i:H.ThinP):0≤result N θ ζ ρ D x l i:=by
  apply mul_nonneg; swap; · exact Tender.pos (Ξ) h hζ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp) _ _
  apply add_nonneg N.balance; unfold tubeRate; have he:=M.fuel; have hr:=(Ξ).active; have hh:=M.sure; positivity
include hr hh
omit he in
lemma bounded (i:H.ThinP) (hv:vetted H i): (∑ p:Orders l,schemePrice N D x θ i p*ρ^p.val) ≤ result N θ ζ ρ D x l i:=by
  let U:= i.val; let Rq:=advantage (Ξ) (K) ζ (n+j) U; let f:=schemePrice (l:=l) N D x θ i; let g:=(1+H.shapeW U)^(n+j)
  have hg:0≤g:=by unfold g; have h':=H.positive_volume U; positivity
  let v:=tubeRate x D r l j
  let k'' := K; have hk:1 ≤ k'':=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
  let u:=entry (Ξ) k'' ζ; have heq:Rq=(∏ i∈U,u i)*g:= if_pos ((H.attends _).2 hv.1)
  have hQ:0 ≤ Rq:= Tender.pos _ h hζ hk _ _
  have hV : 0≤v:=by unfold v tubeRate; have he:=M.fuel; have hr:=(Ξ).active; have hh:=M.sure; positivity
  change (∑ p:Orders l,f p*ρ^p.val)≤(B+v)*Rq; rw [add_mul]
  unfold f schemePrice; by_cases hd:Clear i.val
  · simp_rw [if_pos (show live H i from ⟨hv,hd⟩)]
    apply le_trans _ (le_add_of_nonneg_left (mul_nonneg N.balance hQ)); apply (money (fare N x D θ i.val) (baseN N M hθ) hp).trans
    let f:=fun p:Paint U l=> forge (Ξ) θ p *ρ^inserts p
    change (∑ p: Paint U l, (forge (Ξ) θ p*v*g)*ρ^inserts p)≤v*Rq
    have ha p : (forge (Ξ) θ p*v*g)*ρ^inserts p=v*(g*f p):=by unfold f; ring
    simp_rw [ha]; rw [← Finset.mul_sum, ← Finset.mul_sum, mul_comm g, heq]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (inflated _ hB h hζ hθ _ (isPure hd) hp hs) hg) hV
  unfold Clear at hd; push Not at hd; obtain ⟨q,hq,hQ'⟩:=hd
  simp_rw [if_neg (show ¬live H i from fun h=> hQ' (h.2 q hq))]; rw [Finset.sum_eq_single_of_mem (perch l) (mem_univ _),if_pos ⟨rfl,hv⟩]; swap
  · intro y hy hh; rw [if_neg (fun h=> hh h.1),zero_mul]
  set z:= (∏ i∈U, (Ξ).fare i)
  have hj : (Ξ).meant U (n+j)= z*g:= if_pos ((H.attends _).2 hv.1)
  change B * (Ξ).meant U (n+j)*ρ^(l+1) ≤ _
  apply le_trans _ (le_add_of_nonneg_right (mul_nonneg hV hQ)); rw [hj,mul_assoc, mul_right_comm z, mul_comm z,heq]; apply mul_le_mul_of_nonneg_left _ N.balance
  have Hq : ρ^(l+1)*z≤ ∏ i∈U,u i:=by
    unfold z; rw [← mul_prod_erase U _ hq,← mul_prod_erase U u hq,← mul_assoc]
    apply mul_le_mul (((mul_le_mul_of_nonneg_right hr ((Ξ).fares _))).trans (polluter_cost _ h hk U hv.2 hh hq hQ'))
      (prod_le_prod (fun _ _=> (Ξ).fares _) (fun _ _=> cheap _ h hζ hk _)) (prod_nonneg fun _ _=> (Ξ).fares _) ((Ξ).fares q|>.trans (cheap _ h hζ hk q))
  exact mul_le_mul_of_nonneg_right Hq hg
end Price
end YM.LocalTaylorR2
