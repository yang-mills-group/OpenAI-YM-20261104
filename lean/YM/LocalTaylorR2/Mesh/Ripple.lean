import YM.LocalTaylorR2.Mesh.Emboss
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
namespace Mesh
open Price
variable {j k n l : ℕ} {v r d A a x B D C' ζ η θ c' q w ρ: ℝ} {χ : Chi}
variable (L' : LogIndex c f→ Port.Test T)
variable (N:Captain H j C' d v w A a r B q (n+j) χ)
set_option quotPrecheck false
local notation "Ξ" => N.conduit
variable (hB: LocalBookingsR2 ζ c' N.conduit) (M:StoresR2 H j v d A D k x n χ)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hp:1≤ρ)
    (hθ:1≤θ) (he:Carry l j θ)
variable (hs:ρ*c'≤1) (hr: ρ^(l+1) ≤ betaF G s L^ζ) (hh:betaF G s L^ζ ≤ Real.exp (Q.costs L μ R.beta s C').markSeed)

def cFare (N:Captain H j C' d v w A a r B q (n+j) χ) (x D θ ρ:ℝ) (U : Molecule S) (p:Paint U l):= intricate N.conduit θ ρ p*tubeRate x D r l j*(1+H.shapeW U)^(n+j)
def sfPrice (D x θ ρ:ℝ) (i : H.ThinP) (p:Orders l):ℝ:=if live H i then convolve p (cFare N x D θ ρ i.val) else if p=perch l ∧ vetted H i then B* (Ξ).meant i.val (n+j) else 0
include M hθ hp
lemma baseN {U} (p:Paint U l):0≤cFare N x D θ ρ U p := by
  unfold cFare tubeRate; have hp0 := M.sure; have hr:= (Ξ).active; have hx := H.positive_volume U; have he:= intricate_pos (Ξ) p (zero_le_one.trans hθ) (zero_le_one.trans hp); have hz:= M.fuel; positivity
lemma positional (i:H.ThinP)(p:Orders l): 0 ≤ sfPrice N D x θ ρ i p:=by
  unfold sfPrice; split
  · exact Finset.sum_nonneg fun _ _=> baseN N M hp hθ _
  split
  · exact mul_nonneg N.balance ((Ξ).meant_nonneg ..)
  exact le_rfl

variable (hCr:Crib L' N.conduit l ρ)
include hB h hζ he hs hCr in
lemma muster (i:H.ThinP) (p:Orders l) (V:Config G c) (hv:Healthy (Pressure.temp s) (H.smallAt i) V): Ore V (issue H L' χ i p) v (sfPrice N D x θ ρ i p) j:= by
  unfold sfPrice; split
  next hf=>
    have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hB.leases.hit 0)) hp).trans hs
    have hh(p':Paint i.val l): Ore V (episode H χ i.val (Mesh.warm H L' p')) v (cFare N x D θ ρ i.val p') j:= by
      have hb:0≤2*r*(l+3:ℝ):=by have hq:=(Ξ).active; positivity
      have hw:= holds M _ (intricate_pos (Ξ) p' (zero_le_one.trans hθ) (zero_le_one.trans hp)) hb _ (sumWarm L' N.conduit hB hCr h hζ hp hs he p' (Subset.refl _) hf.1.2)
      exact episodeCost H N.oboe i.2.2 (mantle _ (fun i=>hCr.kept _) _ (Subset.refl _)) hw V hv
    intro E _ _ _ U x hz hV; apply Brush.shimmy _ (Mesh.realized H L' χ i hCr.kept N.oboe hf p E U x hV (hz.symm ▸ hv))
    unfold Mesh.ode; simp_rw [if_pos hf]; exact Brush.spree _ (fun p' v=> episode H χ i.val (Mesh.warm H L' p') (U v)) _ zero_le_one fun i _=> hh i E U x hz hV
  next hf=> split
            next hU=> rw [Mesh.ungrown H L' χ i hf hU.1]; exact (N.collective i V).2 hv
            next hh=> rw [show issue H L' χ i p=(fun _=>0) from by
                        by_cases hv:vetted H i
                        · exact fallow H L' χ i hf fun hx=> hh ⟨hx,hv⟩
                        exact adream H L' χ i hv p]
                      intro E _ _ _ U x h hp; exact (Brush.certified zero_le_one 0).climb (norm_zero.le) le_rfl
-- contaminated if not live (structural invalid has identically zero prices).
-- account
local notation "K"=> ((l+1:ℝ)*θ*ρ)
include h hζ hr hh in
lemma bounded (i:H.ThinP) (hv:vetted H i): (∑ p:Orders l,sfPrice N D x θ ρ i p*ρ^p.val) ≤ result N θ ζ ρ D x l i:=by
  let U:= i.val; let Rq:=advantage (Ξ) (K) ζ (n+j) U; let f:=sfPrice (l:=l) N D x θ ρ i; let g:=(1+H.shapeW U)^(n+j)
  have hg:0≤g:=by unfold g; have h':=H.positive_volume U; positivity
  let v:=tubeRate x D r l j
  let k'' := K; have hk:1 ≤ k'':=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
  let u:=entry (Ξ) k'' ζ; have heq:Rq=(∏ i∈U,u i)*g:= if_pos ((H.attends _).2 hv.1)
  have hQ:0 ≤ Rq:= Tender.pos _ h hζ hk _ _
  have hV : 0≤v:=by unfold v tubeRate; have he:=M.fuel; have hr:=(Ξ).active; have hh:=M.sure; positivity
  change (∑ p:Orders l,f p*ρ^p.val)≤(B+v)*Rq; rw [add_mul]
  unfold f sfPrice; by_cases hd:Clear i.val
  · simp_rw [if_pos (show live H i from ⟨hv,hd⟩)]
    apply le_trans _ (le_add_of_nonneg_left (mul_nonneg N.balance hQ)); apply (money (cFare N x D θ ρ i.val) (baseN N M hp hθ) hp).trans
    let f:=fun p:Paint U l=> intricate (Ξ) θ ρ p *ρ^inserts p
    change (∑ p: Paint U l, (intricate (Ξ) θ ρ p*v*g)*ρ^inserts p)≤v*Rq
    have ha p : (intricate (Ξ) θ ρ p*v*g)*ρ^inserts p=v*(g*f p):=by unfold f; ring
    simp_rw [ha]; rw [← Finset.mul_sum, ← Finset.mul_sum, mul_comm g, heq]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (inflates _ h hζ hθ hp (isPure hd)) hg) hV
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

include hB h hζ he hs hh hr hCr in
lemma consignment : ReadyAll (H:=H) (l:=l) χ (issue H L' χ) v j (sfPrice N D x θ ρ) (result N θ ζ ρ D x l) ρ := by
  refine ⟨fun i p=> Mesh.indexed H L' χ i hCr.kept p,muster L' N hB M h hζ hp hθ he hs hCr,hp,positional N M hp hθ,fun i=>?_,fun i V=> floorplan H L' χ i V l⟩
  by_cases hf:vetted H i; · exact bounded N M h hζ hp hθ hr hh i hf
  simp only [sfPrice,live,hf,false_and,and_false,ite_false,zero_mul,sum_const_zero]; exact tall N M h hζ hp hθ i
end Mesh
end YM.LocalTaylorR2
