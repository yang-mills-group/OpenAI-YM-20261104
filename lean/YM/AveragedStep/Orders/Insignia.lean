import YM.AveragedStep.Orders.Approx
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{P:Patch}{K:KernelChoices}{S:StepData c f}
variable (F:Forest S.ratio)(Q:Cuff S.patch S.kernel A)(x:Site c)(j:F.Free)(i:G.ColorIndex)
-- price distance uniformly in all word geometries (relative to ONE root)
def steps (b:Site f)(w:List (Ink G c f)):ℝ:=(w.map fun i=> (separation b (atRim S i.1):ℝ)).sum
lemma step_pos (b:Site f)(w:List (Ink G c f)): 0≤ steps (S:=S) b w:=by
 induction w with
 | nil=>simp [steps]
 | cons a w ih=> exact add_nonneg (Nat.cast_nonneg _) ih
lemma step_take (b:Site f)(w:List (Ink G c f))(i)(h:i∈w): (separation b (atRim S i.1):ℝ)≤steps (S:=S) b w:=by
 induction w with
 | nil=> cases h
 | cons a w ih=>
   change _≤ (separation b (atRim S a.1):ℝ)+steps (S:=S) b w
   rcases List.mem_cons.mp h with rfl|h
   · exact le_add_of_nonneg_right (step_pos b w)
   exact (ih h).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))
def tolls (x:Site c)(e:Rim c f)(w:List (Ink G c f)):ℝ:= (separation (S.ratio.embed x) (atRim S e):ℝ)+steps (S:=S) (S.ratio.embed x) w
lemma aisle_reach (x:Site c)(e:Rim c f)(w:List (Ink G c f)):
    WithinReach (S:=S) x ((cap (2*aperture S.patch) rimCount)+w.length)
      (tolls (S:=S) x e w+ 2*aperture S.patch) (aisle (S:=S) e w):=by
 constructor; swap
 · unfold tolls; have he:=step_pos (S:=S) (S.ratio.embed x) w; positivity
 · exact Finset.card_union_le ..|>.trans (Nat.add_le_add (home_count S _) (List.toFinset_card_le ..|>.trans_eq (List.length_map _)))
 intro p hi; rcases Finset.mem_union.mp hi with hi|hi
 · unfold tolls; have hp:=separation_triangle (S.ratio.embed x) (atRim S e) (atRim S p); have hh:=reach_home S e hi; have h':(separation (S.ratio.embed x) (atRim S p):ℝ) ≤ (separation (S.ratio.embed x) (atRim S e):ℝ)+2 * (aperture S.patch:ℝ) := by exact_mod_cast hp.trans (Nat.add_le_add_left hh _)
   linarith only [h',step_pos (S:=S) (S.ratio.embed x) w]
 obtain ⟨i,h,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
 apply (step_take (S:=S) (S.ratio.embed x) w i h).trans
 unfold tolls; have he:= Nat.cast_nonneg (α:=ℝ) (aperture S.patch); have hh:=Nat.cast_nonneg (α:=ℝ) (separation (S.ratio.embed x) (atRim S e)); linarith

-- rare term tub; main arbor. X full log fields all z, not independently rebuilt at each p
set_option quotPrecheck false
local notation "v✦" => fingers G i
local notation "e✦" => (Sum.inl j.val:Rim c f)
def tub (w:List (Ink G c f))(d:ℕ)(τ:ℝ)(z:TopologyQ F G):ℝ:=
   let X:=hands F Q x τ z; let V:=vice (S:=S) (A:=A) τ⁻¹ (fieldKey F j i) w d X
   (live F Q x j z-1)*V + τ⁻¹*outerGate F Q x j z*Q.incline (v✦) (F.drape z.1 j.val)*mon w X

def arbor (w:List (Ink G c f))(d:ℕ)(τ:ℝ)(z:TopologyQ F G):ℝ:=
    τ⁻¹ * sdEq F Q x (mon w) j (v✦) τ z - vice (S:=S) (A:=A) τ⁻¹ (fieldKey F j i) w d (hands F Q x τ z) - tub F Q x j i w d τ z
lemma pair_safe (w:List (Ink G c f))(d:ℕ)(τ:ℝ)(hA:LocalRatio A): Envelope (tub F Q x j i w d τ) ∧ Envelope (arbor F Q x j i w d τ):=by
 have hf : Measurable fun z:TopologyQ F G=> F.drape z.1 j.val:= ((continuous_apply j.val).comp (F.continuous_drape.comp continuous_fst)).measurable
 have hL(s : Finset (Rim c f)): Envelope (fun z:TopologyQ F G=> ∏ l∈s,Cuff.ticket Q (aboard F x z l)):= env_product s _ (fun l _=> env_comp Q.ticket_paid (((continuous_apply l).comp (aboard_cont F x)).measurable))
 have hV:=vice_env F Q w x (fieldKey F j i) d τ
 have he:Envelope (tub F Q x j i w d τ):=by
    unfold tub; simp_rw [sub_eq_add_neg]; exact ((hL _|>.add (Envelope.const _)).mul hV).add
       ((((Envelope.const _).mul (hL _)).mul (env_comp (Q.incline_env _) hf)).mul (hands_env F Q x τ _ (mon_cont w).continuous))
 constructor; exact he
 unfold arbor; simp_rw [sub_eq_add_neg]; exact (((Envelope.const _).mul (sd_safe F Q x _ (mon_cont w) j (v✦) τ hA)).add hV.neg).add he.neg -- .. hA

variable {Q} {B D δ:ℝ}(H:Cadence Q B D δ)
include H
lemma tub_corner (w:List (Ink G c f))(d:ℕ)(τ:ℝ)(z:TopologyQ F G)(h:tub F Q x j i w d τ z≠0):CoverHit F x (aisle (S:=S) (e✦) w) δ z:=by
 by_contra he; apply h; unfold tub live
 have hx(l)(ht:l∈home S (e✦)):=H.confirm _ (lt_of_not_ge (show ¬δ ≤ G.chord (aboard F x z l) from fun h=> he ⟨l,aisle_home (e✦) w ht,h⟩))
 rw [show (∏ l∈home S (e✦),Cuff.ticket Q (aboard F x z l))=1 from Finset.prod_eq_one fun l h=> (hx l h).1,
     show Q.incline (v✦) (F.drape z.1 j.val)=0 from (hx _ (home_self S (e✦))).2 _]
 ring
end YM.AveragedStep
