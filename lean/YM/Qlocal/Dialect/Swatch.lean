import YM.Qlocal.Dialect.Voiture
import YM.Qlocal.Reckoner.Translation
/-!
 # Repainting marker ledger in **formal Fk projection** at stated powers. Complements Epoch lore; Keeper controls observation.
 Permit even multiple senses as needed to reach genuine amplitude & λ Epoch Budgets. Transport functional.He.On.Clock across contribution choice via *one* UInt projection per Fiat, no Theta price assertions yet. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function Finset Set
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Assembly
open Function Filter Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Next.Fluctuations Next.SectorChange Multi PertExtension.Series
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V I J K : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [Fintype I][Fintype J][Fintype K]
variable {G:Gauge} {c f:Side}
variable {R:Census I}{X:Census K}
namespace Exhibit
open Join Bulk Keeper
open Reckoner Reckoner.Planet
variable (δ:J→Multi.Hot R) (χ: Colors R G f)
local notation "Y"=>Multi.Hot R
local notation "Λ"=>Planet.Whole J
set_option quotPrecheck false
local notation "Δ"=>fun i:J=> (δ i).val
noncomputable def room (v:J→ℂ)(η:J→ℝ→ Config G f→ℂ) (i:Y) : ℝ→ Config G f→ℂ:= ∑ j∈univ.filter (fun x=>δ x=i),v j • η j
noncomputable def knot (j:J) : Multi.Hot (Whole J):=⟨Planet.pack {j},singleton_nonempty _⟩
lemma unique : Injective (knot:J→Multi.Hot (Whole J)):= fun _ _ h=> singleton_inj.mp (congr_arg (fun i:Multi.Hot (Whole J)=> i.val.val) h)
variable (f₀:J→ℝ→ Config G f→ℂ)(v:J→ℂ)
local notation "r'"=> Exhibit.room -- for m_Ph!
-- `Funding`: Compile on census J unaltered.May include blanks.
noncomputable def shadow : Bulk.Colors (Whole J) G f:= {vac:=χ.vac, mark:= fun i=> if hi:i∈ Set.range (knot : J→Multi.Hot (Whole J)) then f₀ hi.choose else 0,power:= fun i=>if hi:i∈ Set.range (knot:J→Multi.Hot (Whole J)) then χ.power (δ hi.choose) else 0}
noncomputable def sheets : Bulk.Colors R G f:= { χ with mark:= Exhibit.room δ v f₀ }
local notation "W"=> shadow δ χ f₀
local notation "F"=> sheets δ χ f₀ v
local notation "p"=> (fun i:J=> (δ i).val)
local notation "τ"=>Translation.morph (fun i:J=>(δ i).val) v (fun i: J=> (δ i).prop)
local notation "Cv"=> (fun j: Multi.Hot (Whole J)=> j.val)
private lemma typed (j:J) (hp:knot j∈Set.range (knot:J→Multi.Hot (Whole J))): hp.choose=j:= unique hp.choose_spec
lemma borne (j:J): (W).mark (knot j)=f₀ j ∧ (W).power (knot j)= χ.power (δ j):= by
 dsimp only [shadow]; split
 next h=> rw [typed j h]; exact ⟨rfl,rfl⟩
 next h=> exact (h ⟨j,rfl⟩).elim
lemma dropped (j:Multi.Hot (Whole J))(hj:j∉Set.range (knot:J→Multi.Hot (Whole J))) : (shadow δ χ f₀|>.mark j)=0:=dif_neg hj
variable {S:StepData c f}{π:Clip}{L:PathData G}{O:ChartRatio G}
    (K0:Kernel S π L O)(H:Forest S.ratio)(T':S.Choices)
variable (hf:∀ i,ContDiffAt ℝ ω (posed S H (f₀ i)) 0) (i:ℕ)(x : Bulk.Joint S H (G:=G))
-- Generic criterion.Author.Last.Wire.Port.Core.Owner.Mesh.Cover. marker Op Epoch need pose.L.*. 
abbrev beam (x':J):ℂ:= Assembly.jet (posed S H (f₀ x')) (χ.power (δ x')+i) x
local notation "Fq"=> beam δ χ f₀ H i x
local notation "FF"=> Joint
-- defeq ℂ se.H.We.Geek.Work.
include hf
omit hf in
private lemma jet_lo {N:Type*}[NormedAddCommGroup N][NormedSpace ℝ N] (f:N→ℂ)(h:ContDiffAt ℝ ω f 0)(x:N)(v:ℂ): Assembly.jet (v • f) i x= v* Assembly.jet f i x:= Eq.symm (jet_apply_left ((v:ℂ) • ContinuousLinearMap.id ℝ ℂ) f i (h.of_le le_top) x)
private lemma jet_room (y:Y) : markLetter χ.power (markFn S H (sheets δ χ f₀ v)) y x i= ∑ j∈ univ.filter (fun x=>δ x=y),v j*Fq j:= by
 let P:= univ.filter (fun x=>δ x=y); let f₁ (j:J):= v j • posed S H (f₀ j); have he(j):ContDiffAt ℝ ω (f₁ j) 0:= (contDiffAt_const (c:=v j)).mul (hf j)
 have ht:markFn S H (F) y=∑ a∈P,f₁ a:=by ext x; unfold markFn Bulk.posed sheets room; simp only [Finset.sum_apply]; rfl -- maybe reduces V∧x references.
 unfold markLetter; rw [ht]; unfold Assembly.jet; rw [show iteratedFDeriv ℝ (χ.power y+i) _ _ = ∑ j∈P,iteratedFDeriv ℝ (χ.power y+i) (f₁ j) 0 from ?_]; swap; · exact iteratedFDeriv_sum_apply (fun a _=>(he a).of_le le_top) -- query
 rw [ContinuousMultilinearMap.sum_apply, Finset.smul_sum]; refine Finset.sum_congr rfl fun j hj=>?_; change Assembly.jet _ _ _ = _; unfold beam; rw [(mem_filter.mp hj).2]; exact jet_lo _ _ (hf j) _ _ -- query order
local notation "v'"=> (fun j: Multi.Hot (Whole J)=> markLetter ((W).power) (markFn S H W) j x i)
-- lookup integer not nonlinear.Le.
omit hf
lemma lightbeam (j: J): markLetter ((shadow δ χ f₀).power) (markFn S H (shadow δ χ f₀)) (knot j) x i= beam δ χ f₀ H i x j:= by unfold markLetter markFn; rw [(borne δ χ f₀ j).1,(borne δ χ f₀ j).2]
lemma darkness (j: Multi.Hot (Whole J))(hz:j∉ Set.range (knot:J→Multi.Hot (Whole J))) : markLetter ((shadow δ χ f₀).power) (markFn S H (shadow δ χ f₀)) j x i=0:= by unfold markLetter markFn; rw [dropped _ _ _ _ hz]; have he: posed S H (0: ℝ → Config G f→ℂ)=0:=rfl; rw [he]; simp [Assembly.jet]
lemma disclosed : lit (Whole J) v'= ∑ j:J,Fq j • (Planet.glyph j):= by
 apply Marker.Poly.ext; intro t; rw [Poly.part_sum]; by_cases h:t.val.Nonempty; swap; · have he:t=(Whole J).quiet:= Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h); subst t; rw [part_lit_quiet]; symm; exact Finset.sum_eq_zero fun i _ => by rw [Poly.part_smul, glyph_fire,Poly.part_send,if_neg (fun he:(Whole J).quiet=(Whole J).fire i=> Finset.singleton_ne_empty i (congr_arg Subtype.val he.symm)),mul_zero]
 let k: Multi.Hot (Whole J):=⟨t,h⟩; change (lit _ v' ).part k.val=_; rw [part_lit]; by_cases he:k∈ Set.range (knot:J→Multi.Hot (Whole J));
 · obtain ⟨u,hu⟩:=he; rw [sum_eq_single u]; · change v' k= (Fq u • Planet.glyph u).part k.val; rw [← hu]; dsimp only; rw [lightbeam, Poly.part_smul]; change _= _ * ((Poly.send (knot u).val 1).part _); simp
   · intro j hj hj'; change (_ • Planet.glyph _).part k.val=_; rw [Poly.part_smul, glyph_fire, Poly.part_send, if_neg, mul_zero]; exact fun hv:k.val=(knot j).val=>hj' (unique ((Subtype.ext hv.symm).trans hu.symm)) -- k=W.whole
   simp
 rw [darkness δ χ f₀ H i x k he]; symm; exact Finset.sum_eq_zero fun i _=> (by rw [Poly.part_smul,glyph_fire,Poly.part_send,if_neg,mul_zero]; exact fun hv:k.val=(knot i).val=>he ⟨i,Subtype.ext hv.symm⟩)
include hf
lemma transported : τ (lit (Whole J) v')=lit R (fun j=>markLetter ((F).power) (markFn S H F) j x i):=by
 rw [disclosed,map_sum]; apply Marker.Poly.ext; intro t; by_cases h:t.val.Nonempty; swap; · have he:t=R.quiet:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp h); rw [he,part_lit_quiet,Poly.part_sum]; exact sum_eq_zero fun i _=> by rw [map_smul, Translation.issues (p) v, Poly.part_smul, Poly.part_send,if_neg,mul_zero]; exact fun hv:R.quiet=(δ i).val=> (δ i).prop.ne_empty (congr_arg Subtype.val hv.symm)
 let u: Multi.Hot R:=⟨t,h⟩; change (∑ j:J,τ (Fq j • Planet.glyph j)).part u.val = (lit R _).part u.val; rw [part_lit, (show markLetter ((F).power) (markFn S H F) u x i= ∑ j∈univ.filter (fun j=>δ j=u), v j* Fq j from jet_room δ χ f₀ v H hf i x u), Poly.part_sum,sum_filter]; refine Finset.sum_congr rfl fun y _=>?_; rw [map_smul,Translation.issues (p) v,Poly.part_smul,Poly.part_send]
 by_cases h:u=(δ y); · simp only [h,if_true,true_and]; rw [mul_comm]
 rw [if_neg (fun he=>h (Subtype.ext he)),if_neg (Ne.symm h), mul_zero]
end Exhibit
end YM.Qlocal.Dialect
