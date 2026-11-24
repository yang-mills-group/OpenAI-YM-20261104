import YM.LocalTaylorR2.Exponent.Vast

/-!
 # Unprofiled logarithmic Haar factor. Keep epoch post mean & determinant row choice (not a conventional-g diagonal) in gauge. Follow Mesh/Pigment upto Profile...
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Mesh Work.G05
variable {i:Bond f}{X:Coat T F}
def innerHa (_H:Cash W s μ L Q o C T R)(p:ℕ)(i:Bond f) : Port.Test T:= fun _ X w=>if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then curved Q.table p (worldZ X R.beta w i) else 0
-- true pushed Haar-X0 model except uncertainty at seam `dark`; not extrapolating Tilt Γ support. Applies even where dim, cost at lenses. 
variable (H) (i j)
lemma inheritHa : Port.Burst H (H.supportP (identityLog (soloLetter i))) (innerHa H j i):=by
  constructor
  · intro F X X' w v ht hK Z hh hl hV
    have hT : Room P S T X.x:= ht.symm ▸ H.laws.data.room
    let A: Borough X X' Z w v ∅ ∅ R := ⟨hl,(observe _).1 hV,fun _ _=> Iff.rfl⟩
    have hy : town S X.B Q.halo i⊆ Z:= by unfold Coat.B; rw [ht]; exact hh
    have hq (a:ℕ)(h:a≤400): Cleanroom Z (a*X.B) (atEdge S i):=fun j hj=> town_circle hy j <| hj.trans (Nat.mul_le_mul_right _ (by have hh:=Q.buys; omega))
    obtain ⟨hp,hz⟩:=A.occupied hT i (hq 400 le_rfl)
    unfold innerHa; simp_rw [hp,hz,(A.hair hT i (hq 25 (by omega)) _).2]
  · intro E _ F X hx hk V Y w hp hv ht
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    have hs := (compassBro hr.ready hp X hv (show ShellAccess S G X.x W X.width o.γ from (by rw [hx,hk]; exact H.laws.data.access)) R.beta).2.2 _ ht
    let z t:= worldZ (Art.drive X (V t) (Y t)) R.beta (w t)
    change Measurable fun t=> if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then curved _ j (z t i) else 0; split
    · exact (blockTaylor_contDiff _ _ 0).continuous.measurable.comp ((measurable_pi_apply i).comp hs)
    exact measurable_const
  · intro F X hx hk _ z w; unfold innerHa; have h: ShellAccess S G X.x W X.width o.γ:=by rw [hx,hk]; exact H.laws.data.access
    rw [Stained.flight X z (show P.Funds S T from H.laws.intake.ready) h]; split
    · rename_i he; rw [if_pos (show i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i from he)]; exact Mesh.halo Q.table_exists (z (atEdge S i)) (worldZ X R.beta w i) (p:=j)
    next he=> exact (if_neg he).symm
  intro F X hx hk hX n b A E _ _ _ V x hp hv ht Z he; subst s; change Drifts _ (fun t y=> if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then curved Q.table j (worldZ _ _ (course _ _ _ _ _) i) else 0) x n; split_ifs
  swap; · exact Drifts.fat (Zest.still _)
  have hi:i∈ edgesM S Z X.B:= mem_filter.mpr ⟨mem_univ _,fun y hy=> town_circle (show town S X.B Q.halo i⊆ Z from he) _ (hy.trans (Nat.mul_le_mul_right _ (by have h:=Q.buys; omega)))⟩
  exact (chording X R.beta i hp H.laws.data.room hv H.laws.intake.positive Z hi).taylor (towerMax Z X.B) _ _
lemma outerlaw (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(o:Target.Order G W)(χ:Chi)(j p:ℕ)(d:ℝ→ℝ)(hd:Rate G L (-(1/2)) d) : ∃ b,Rate G L 0 b ∧ ∀ᶠ x in atTop, ∀ c f (S:StepData c f)(T:Tube G S)(R:Rep G f) μ C (H: Cash W x μ L Q o C T R)(i:Bond f)(v:ℝ), Astonish H (town S (radiusB x) Q.halo i) j (p+j) v (d x) χ (|b x|) 1 (innerHa H p i-quanta H p i):=by
  obtain ⟨B,hB,hP⟩:= Clutch.kernels G L χ hd j (2*o.a)
  let J: G.Color→ ℝ:= fun x=>Real.log (Q.table.J x); let hÑ:= Q.table_exists
  obtain ⟨M,hM,hp⟩:= Brush.neighborhood (k:=p) 0 (show ContDiffAt ℝ p J 0 from ((hÑ.germ 0 (Metric.mem_ball_self hÑ.patch)).of_le le_top).log (by rw [hÑ.anchored]; norm_num))
  let a x:= 1+(d x+o.cap*Pressure.fiery G x L+2*Fintype.card G.ColorIndex)
  let g x:= M*|stamp j p 1 (a x)| *2; let f x:= g x*(1+(|B x|+1))^j
  have hz : Rate G L 0 a:= (Rate.const 1).add ((((hd.add (Rate.flame.mul_left _)).weaken (by norm_num))).add (Rate.const _))
  have hh {g:ℝ→ℝ}(h:Rate G L 0 g) := h.compare (v:=fun x=>|g x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  have hg:Rate G L 0 g:= ((hh (rateStamp _ _ hz)).mul_left M).mul_right _
  refine ⟨f,?_,?_⟩
  · simpa only [zero_mul,zero_add] using! hg.mul (((Rate.const 1).add ((hh hB).add (Rate.const 1))).pow j)
  filter_upwards [hP] with x ht c f' S T R μ C H i v
  refine ⟨(inheritHa H p i).sub (Port.Burst.fat (sealH (H:=H) (p:=p) (i:=i))),?_⟩
  intro E _ _ _ F X V u z y w hX hW hΨ hχ _ hu U hU; subst x; let hT:= H.laws.data; have hv:0<X.t:=hT.room.fiery; have hwS:=hT.funds.length_eq
  let Z':=edgesM S U X.B; let Z:=facescale Z' w; have hZ:1≤Z:= (Flux.expenses ..).1
  let q t:= (innerHa H p i-quanta H p i) F (vary X (V t)) (z t); have hL : 0≤|f X.x| *Z^(p+j):=by positivity
  have he:= hu.price; have hh :1≤ a X.x:= by unfold a; rw [←hwS]; have hM:= hT.safety.1; change 1≤1+(d X.x+o.cap*X.t+_); exact le_add_of_nonneg_right (by positivity)
  by_cases hk: i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i; swap
  · have hp:q=ᶠ[𝓝 y] 0:=Eventually.of_forall fun t=>by change (if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then _ else _) - profile _ _ X _ _ _ =0; simp only [Mesh.profile,if_neg hk,sub_zero]
    exact ⟨Brush.zi hp hL zero_le_one,fun _=>hp⟩
  have hi:i∈ Z':= mem_filter.mpr ⟨mem_univ _,fun j hj=> town_circle (show town S X.B Q.halo i⊆U from hU) _ (hj.trans (Nat.mul_le_mul_right _ (by have h:=Q.buys; omega)))⟩
  constructor
  · have hhM := (ht c f' S T F X rfl hwS hχ (by have h:=o.large; positivity) _ w _ _ y V u z hu i)
    let y' t:= 1-X.cone (2*o.a) (u t) i; have hy : Brush j 2 (|B X.x|) y' y:= ( ((Brush.certified hhM.pos (1:ℝ)).separating hhM)).climb (by norm_num) le_rfl
    have hZ': Brush j (a X.x*Z) 1 (fun y=> u y i) y:=by
       apply (ranges i hi H hΨ hW hu).climb _ le_rfl; unfold a; rw [←hwS]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
    have hp' : Brush j (M*(|stamp j p 1 (a X.x)| * Z^(p+j))) 1 (fun y=>curved Q.table p (u y i)) y:= by
       apply (tactile J hp.self_of_nhds hZ' (one_le_mul_of_one_le_of_one_le hh hZ)).climb _ le_rfl; apply (upperShape M _ _ p j hh hM.le hZ).trans; gcongr; exact le_abs_self _
    apply (((hy.paints hp').trim).climb (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_abs_self (f X.x)) (by positivity : 0≤ Z^(p+j)))) le_rfl).shimmy
    · apply Eventually.of_forall; intro t; change (if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then _ else _) - profile _ _ X _ _ _ = _; unfold Mesh.profile; rw [if_pos hk, if_pos hk, hu.moving]; unfold y'; ring
    unfold f g; ring
  intro hf; filter_upwards [smallG U H hΨ hW hu hf] with t ht; change (if i∉X.plaza (X.seeds.dome (304*X.B)) ∧ X.Hot i then _ else _) -profile _ _ X _ _ _ =0; rw [if_pos hk,Mesh.profile, if_pos hk,hu.moving]; rw [ht i ((mem_filter.mp hi).2 (atEdge S i) (by simp)),one_mul,sub_self]
end YM.LocalTaylorR2.Exponent
