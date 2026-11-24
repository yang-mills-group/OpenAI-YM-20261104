import YM.FVA2.Clef.Winds
/-!
 # Unscaled position-frame scale group is actually smooth through every order

 `Instant` at EVERY time with its infinitesimal generator. `b0` and check-gau derived as
 in `Drive`. Deduce C∞ at each order by induction with generator RHS. A linear position-frame
 part is allowed; not claiming `B` is itself already dimension-preserving. Evaluates in every
 context of the portal.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
section analytic
variable {A: Arenas G}{p:ℝ→Cn}{U:ℝ→Frames G}
variable (H:Touched A p U)(B:Guard G d)(h:Instant (fun i=>U i d) B 0)
include H h
theorem time (t:ℝ): Instant (fun i=> U i d) ( weight (U t d)+ U t d * stepV (p t) B ) t:= by
    let F(s:ℝ):= convertT s (U t d)*stepV (p t) (U s d); have he(s):F (s-t)=U s d:= by unfold F; rw [ ← (H.additive t (s-t)).2 d, add_sub_cancel .. ]
    have hx:= combine ( applyD (U t d)) ( h.shift ( p t ) ); rw [ H.ground.2, Scale.Frame.step_one,mul_one, neutral ] at hx
    intro n v; let q:= v (coeff n (weight (U t d)+ U t d * stepV (p t) B)); obtain ht:=hx n v; change HasDerivAt (fun s=>v (coeff n ( F s ))) q 0 at ht; rw [ ← sub_self t ] at ht; obtain H:= ht.scomp (h:=fun s:ℝ=> s-t) t ( (hasDerivAt_id' t).sub_const t ); simp_rw [Function.comp_def,he,one_smul] at H; exact H
omit h H in
lemma smoothX (hp:Clear p): ∀ (n:ℕ), ContDiff ℝ ∞ (fun t=> coeff n (p t)) := by
    intro n; obtain ⟨A,h⟩:= Rhythm.from_poly.mp ( Rhythm.unit.mpr ( hp n ) ); rw [h]; simp_rw [Polynomial.eval_eq_sum,Polynomial.sum]; apply ContDiff.sum; intro j _; exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.pow j))
variable (hp:Clear p)
include hp
lemma pays : ∀ l i:ℕ,∀ v:Module.Dual ℂ (FieldEnd G d), ContDiff ℝ l (fun t=> v (coeff i ( U t d ))):= by
    intro l; induction l with
    | zero=> intro i v; apply contDiff_zero.mpr; refine Differentiable.continuous (𝕜:=ℝ) ?_; intro x; exact ( time H B h x i v ).differentiableAt
    | succ l ih=>
      intro i v; let A(t:ℝ):= U t d; let f(t:ℝ):= v (coeff i (A t)); have hF(t): HasDerivAt f (v (coeff i ( weight (A t) + A t * stepV ( p t ) B ))) t:= time H B h t i v
      -- recurrence RHS continuous at l from ih
      rw [ Nat.cast_succ ]; apply contDiff_succ_iff_deriv.mpr; refine ⟨ fun x=> (hF x).differentiableAt,?_,?_⟩; · simp -- not ω?
      change ContDiff ℝ (l: WithTop ℕ∞) (deriv f); rw [ show deriv f=_ from funext (fun x=> (hF x).deriv ) ]; simp_rw [map_add]; refine ContDiff.add ?_ ?_
      · simp_rw [ weight,map_sub,coeff_C_mul,coeff_mul_C ]; exact ContDiff.sub ( ih _ ( v ∘ₗ LinearMap.mulLeft ℂ _ ) ) ( ih _ ( v ∘ₗ LinearMap.mulRight ℂ _ ) )
      simp_rw [coeff_mul,map_sum]; refine ContDiff.sum ?_; intro j _; unfold stepV; simp_rw [coeff_mk,rules,Finset.mul_sum,mul_smul_comm,map_sum,_root_.map_smul ]; refine ContDiff.sum ?_; intro k _; exact ( ( contDiff_infty.mp ( smoothX (p:=fun t => p t ^ k) (hp.pow k) j.2 ) l ).smul ( ih _ ( v ∘ₗ LinearMap.mulRight ℂ _ ) ) )
end analytic
variable (ν:ℝ){Y:Initialize G}{V: Normalize.Store G}{K: Rose.Pick V}
variable {T: MS_Data G ( Position.OpenAxis.Plot (Press.portDeck G))}
variable {S: Prescription (Press.portDeck G)} (h:G.Simple)(H:System.Contract Y K T S)
local notation "B"=>Scale.GroupS.gaugeB K T ν
local notation "γ"=>Scale.GroupS.ψ K T ν
local notation "W"=>Generator.Drive.engraving B
include h H
lemma evolves (d:ℕ)(t:ℝ): Instant (fun i=> B i d) (weight ( B t d )+ B t d * stepV (γ t) ( W d ) ) t:= time ( growsV h H ν ) _ (field_X h H ν) t
lemma Bach (v:Module.Dual ℂ (FieldEnd G d))(i:ℕ): ContDiff ℝ ∞ (fun t=> v (coeff i (B t d))) := contDiff_infty.mpr ( fun l=> pays ( growsV h H ν ) _ ( field_X h H ν ) ( scalesE H ν|>.smooth ) l i v )
lemma harmony : Generator.Drive.engraving ( Scale.GroupS.gaugeN Y K T ν ) d = casting ( Scale.Measure.adjust Y K d ) (Scale.Beta.beta γ) ( W d ):= by apply derivative_eq; rw [ originate h H ν ]; exact casted_c ( growsV h H ν ) ( fun _=> real H ν ) ( length_w h H ν ) ( scalesE H ν|>.smooth ) ( field_X h H ν (d:=d) )
end YM.FVA2.Clef
