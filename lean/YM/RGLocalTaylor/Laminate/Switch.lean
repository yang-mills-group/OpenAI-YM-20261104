import YM.RGLocalTaylor.Laminate.Winding
import YM.MergeProof.Sate

/-!
# Read full nilpotent exponent in the ACTUAL prior measure and post-price format
Includes real and imaginary histories with any overlaps/channels. This operator
is linear in each assignment even though the reference Gaussian averages need
not factor (keeps the original `fragrance`). Coefficients defined before
any Taylor horizon derivative costs and on full marker polynomials. Then off-mask
permit is explicit; derivative estimates will apply to the unmasked germ here,
not try to push a derivative through such a permit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March
namespace Laminate
open RG01.Survive Mayer Trees Merge Palette Gas Ursell Marker
variable {κ ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (N : Captain H j C' d v Y A b r B q n χ)
    {p:H.ThinP}[DecidableEq κ]{R':Marker.Census κ}(y:ι→Poly R')(hy:∀ i,y i*y i=0)(hu:∀ i,(y i).part R'.quiet=0)
    (w:H.fragrances)(U:Config G c)(hP:Plot M' H rA)
abbrev Flight (w:H.fragrances)(k:ℕ):= (Option (Fin w.fst)) → VoucherL M' S k
def tax : ℝ:= Ursell.coefficient H.seam w.snd / ↑(w.fst+1).factorial
abbrev mint (Z:H.ThinP) (V : Config G c) (z:VoucherL M' S k) : ℝ:= rector χ H M' rA Z V z
def columnKey (t:Flight M' w k)(U:Config G c):= tax w * ∏ i, mint M' rA (χ:=χ) (w.2 i) U (t i)
def salary (t:Flight M' w k) : ℕ:=∑ i, (t i).snd.val
local notation "c'" => Palette.song M' H χ rA
-- bodies distinguished (include possible 0 wages and zero label real costs; grouping only transit)
abbrev frame (t:VoucherL M' S k):= ∏ z∈ t.fst.val, y z
def paints (t:Flight M' w k):= ∏ i, frame M' y (t i)
def Pulse' (t:Flight M' w k) :Prop:= ∃ i,(t i).fst.val.Nonempty

def grain (u:Flight M' w k)(V:Config G c) : Poly R':= ((columnKey M' rA w (χ:=χ) u V :ℝ):ℂ) • paints M' y w u
variable (keep:H.fragrances→ ℕ→Prop)

def passenger (u:Flight M' w k):Prop:= Pulse' M' w u ∧ keep w (salary M' w u)

/-- the advertised estimator. No desk motion or censorship. -/
def stained (k:ℕ)(V:Config G c) := ∑ u∈univ.filter (passenger M' w keep (k:=k)),grain M' rA y w (χ:=χ) u V
include N hP
open Merge.Switch

omit hP in
lemma fragment {w:H.ThinP} (ht:Healthy (Pressure.temp s) (H.smallAt w) U)(k:ℕ) :
    sound y (vote M' H χ rA w.val U) = ∑ p:VoucherL M' S k, (↑(mint M' rA w (χ:=χ) U p):ℂ) • frame M' y p := by
  let f (u:VoucherL M' S k):= click u.1.val (mint M' rA w (χ:=χ) U u)
  rw [show vote M' H χ rA w.val U = ∑ i,f i from (by ext p i; rw [warrant χ H _ _ N _ _ _ _ k, masked_eq _ _ _ _ ht]; simp only [Finset.sum_apply]; rfl), Merge.Switch.summed y _ f (fun i=>‖mint M' rA w (χ:=χ) U i‖) (fun i _=> Merge.Switch.paidClick _ (norm_nonneg _) (fun _=>le_rfl))]; exact sum_congr rfl (fun i _=> Merge.Switch.gather y _ _)
omit N hP
lemma spectral (t x): Palette.song M' H χ rA w U t x = tax w * ∏ i, vote M' H χ rA (w.2 i).val U t x:= by
   unfold Palette.song tax Cash.trainedMill Gas.term; ring_nf; rw [mul_right_comm]; rfl
-- to check if parse "omit" only for all lemmas
include N hy hP
-- CLEAN complement w valid (vote.sound price not used). HEALTH used for every letter germ.
lemma timetable (hg:Healthy (Pressure.temp s) (H.bookFoot (.inr w)) U) (k:ℕ) : sound y (c' w U) = ∑ j : Flight M' w k, grain M' rA y w (χ:=χ) j U:= by
  let S i:= vote M' H χ rA (w.2 i).val U; let T:Ways ι:= ∏ i,S i
  have hl v:= Palette.aca M' H χ rA hP (w.2 v) 0
  let a i:= Palette.tune M' H rA 0 0 (w.2 i).val
  have h i:Merge.Switch.Paid (fun _:Unit=>S i) (a i):= (hl i).toPoint _ U
  let Z:= (fun (_t:ℝ)(_p:Finset ι)=> tax w); have he: Merge.Switch.Paid (fun _:Unit=>Z) ‖tax w‖:= Merge.Switch.constant _ (norm_nonneg _) (fun _=>le_rfl)
  have hf : Merge.Switch.Paid (fun _:Unit=>T) (∏ i,a i):=by
     convert! Merge.Switch.Paid.prod univ _ a (fun i _=> h i) using 1; ext1 i; rw [Finset.prod_apply]
  have hh i : Healthy (Pressure.temp s) (H.smallAt (w.2 i)) U := Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ w.2) (mem_univ i)) hg
  rw [show c' w U=Z*T from (by ext t p; rw [spectral]; simp only [Pi.mul_apply,T,Finset.prod_apply];rfl), Merge.Switch.mul_sounds y hy (show Models Z _ from (he.works ()).choose_spec) (show Models T _ from (hf.works ()).choose_spec),const_sounds]
  unfold T; rw [Switch.product y hy _ S a (fun i _=>h i),Poly.product_bead]; unfold S; simp_rw [fragment M' rA N y U (hh _) k] -- arg
  rw [Fintype.prod_sum,Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [Finset.prod_smul,smul_smul]; unfold grain columnKey paints; rw [Complex.ofReal_mul,Complex.ofReal_prod]

omit [Fintype ι] hy N hP in
private lemma unit_part (hu:∀ i,(y i).part R'.quiet=0)(u:Flight M' w k)(hk:Pulse' M' w u) : (grain M' rA y w (χ:=χ) u U).part R'.quiet=0:=by
  obtain ⟨z,hz⟩:=hk; obtain ⟨i,hi⟩:=hz; rw [grain,Poly.part_smul,paints,← mul_prod_erase _ _ (mem_univ z),Poly.quiet_mul]; unfold frame; rw [← mul_prod_erase _ _ hi,Poly.quiet_mul,hu,zero_mul,zero_mul,mul_zero]
omit [Fintype ι] N hP hy in
private lemma hollow (u:Flight M' w k)(hk:¬Pulse' M' w u): paints M' y w u=1:=by
  apply prod_eq_one; intro i _; unfold frame; rw [not_nonempty_iff_eq_empty.mp (fun h=>hk ⟨i,h⟩), Finset.prod_empty]

include hu
omit N hy hP in
lemma bangs (k:ℕ) : (stained M' rA y w (χ:=χ) keep k U).part R'.quiet=0:=by
  unfold stained; rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun i hi=> unit_part M' rA y w U hu i ((mem_filter.mp hi).2).1)
variable {keep}
lemma floorT (k:ℕ) (hx:Healthy (Pressure.temp s) (H.bookFoot (.inr w)) U) :
    ∑ u∈univ.filter (fun t:Flight M' w k=>¬Pulse' M' w t),grain M' rA y w (χ:=χ) u U = Poly.bead R' (↑(c' w U 0 ∅)):= by
  let v u:= Pulse' M' w (u:Flight M' w k); let V:= univ.filter fun u=>¬v u
  let t (u:Flight M' w k):ℂ:= ↑(columnKey M' rA w (χ:=χ) u U)
  let g (u:Flight M' w k):=grain M' rA y w (χ:=χ) u U
  change ∑ u∈ V,g u=_
  have hp (u:Flight M' w k)(he:u∈V):g u=Poly.bead R' (t u):=by unfold g grain; rw [hollow M' y w u ((mem_filter.mp he).2),← Poly.product_bead,mul_one]
  rw [sum_congr rfl hp,← map_sum]; apply congr_arg
  have he: (sound y (c' w U)).part R'.quiet= (↑(c' w U 0 ∅):ℂ):= sunset _ (Palette.fair M' H χ rA hP w 0) _ _ hu
  rw [timetable M' rA N y hy w U hP hx k, Poly.part_sum] at he; refine Eq.trans ?_ he
  refine (Finset.sum_congr rfl (fun i hi=> show t i=(g i).part R'.quiet from ?_)).trans (sum_subset (subset_univ _) (fun p _ hu'=>?_))
  · rw [hp i hi, Poly.bead]; simp -- simp?
  exact unit_part M' rA y w U hu _ (not_not.mp (fun hj=> hu' (mem_filter.mpr ⟨mem_univ _,hj⟩))) -- args

variable (keep)
set_option quotPrecheck false
lemma landing (k:ℕ): Photo.headSheet M' H χ rA R' y w U = masked (Pressure.temp s) (H.bookFoot (.inr w)) (stained M' rA y w (χ:=χ) (fun i n=>¬keep i n) k+stained M' rA y w (χ:=χ) keep k) U:=by
   unfold Photo.headSheet; by_cases hg:Healthy (Pressure.temp s) (H.bookFoot (.inr w)) U
   · let Z:= c' w U; let T:=Photo.tones M' H χ rA w U; let X : Ways ι:= (fun _ _=> Z 0 ∅)
     have hx:Merge.Switch.Paid (fun _:Unit=>X) ‖Z 0 ∅‖:= Merge.Switch.constant _ (norm_nonneg _) (fun _=>le_rfl)
     have ht : Merge.Switch.Paid (fun _:Unit=>Z) _:= (Palette.fair M' H χ rA hP w k).toPoint _ U
     have he : Merge.Switch.Paid (fun _:Unit=>T) _:= ht.sub hx
     rw [masked_eq _ _ _ _ hg]; change sound y T = _; rw [← add_right_cancel_iff (a:= sound y X), ← Switch.add_sounds _ (show Models T _ from (he.works ()).choose_spec) (show Models X _ from (hx.works ()).choose_spec), show T+X=Z from sub_add_cancel Z X, Merge.Switch.const_sounds,← floorT M' rA N y hy hu w U hP k hg] -- names?
     unfold Z; rw [timetable M' rA N y hy w U hP hg k]; symm
     rw [Pi.add_apply]; unfold stained; rw [Finset.sum_filter, Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib,← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_
     by_cases h:Pulse' M' w i
     · by_cases he:keep w (salary M' w i) <;> simp [passenger,h,he]
     simp [passenger,h] -- check
   next =>
      have he t p : Palette.song M' H χ rA w U t p=0:=Classical.byContradiction (fun h=>hg ((Palette.permits M' H χ rA w p t).2.2.2 U h))
      rw [masked_ne _ _ _ _ hg]; rw [show Photo.tones M' H χ rA w U=(fun _ _=>0) from funext fun t=>funext fun p=>(congr_arg₂ (·-·) (he t p) (he 0 ∅)).trans (sub_self _),Merge.Switch.const_sounds]; simp

end Laminate
end YM.RGLocalTaylor
