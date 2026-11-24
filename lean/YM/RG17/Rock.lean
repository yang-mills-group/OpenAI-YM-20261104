import YM.RG17.Valence
/-!
# Pay OPE points also just OFF this lattice. Generic tail variant; no contact. WilsonX series interpolation still needs actual purchase (at priced readouts instead of all measured points). Estimate version for physically determined packet and any forecast when associated costs/hol on axes proved separately. Predict must measure at THESE positions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits OPE.Log Polar Extraction Word Table Metric
open Lattice RG SharpGram PhysicalNext PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{U:Spec.Final R.family f S}{L:Layout U}
variable {B:Filter (ℕ×ℕ)}{D:Lenses.Mantle U B}(Z:Ledger L)(W:Services R.family f S)(fx:Flick R.family.path.levels)(hz:Pegs D L) (P:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
set_option quotPrecheck false
local notation "T"=>OPE.run
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
variable {n:ℕ} (d: Fin n → ℕ)(t:ℕ) (v:ℝ→Labels S d) (p:GradePrice P d v 0)
    (A:Free R.family t→L[ℂ] ℂ) (u:ℝ→ℂ) (ht:RateLE home T u 0)
local notation "Q"=> wheel R.family
include fx Z W hz
lemma shapedOrder (m:ℝ→ℕ)(h:Lookup R m)(ho:Moored R.family L.level) (Hb:∃ u r D,OPE.Log.LogPackage R.family u r D)(j:Fin n) {v:ℝ→(i:Fin n)→R.family.label (d i)} {i:ℕ} (ht:∀ᶠ r in home,∀ j:Fin n,Paid L r (v r) j≤ H (Q r)^i) :
     ∃ (α:ℝ)(Y:ℝ→ℕ)(q A₀:ℝ→ℝ), 0 < α ∧ α<1 ∧ Height R.family.S home T Y α ∧ ValueStamp home T q ∧ RateLE home T A₀ (-((t+1/16:ℝ)*(1-α))) ∧ ∀ x:Points n,x∈generic n→
        (∀ b:ℝ→ Fin n→ Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x)→∃ X:ℝ→R.family.label t,∀ᶠ r in home,∃ (p':Filter (ℕ×ℕ))(y:ℕ×ℕ→ R.family.label t),p'.NeBot∧p'≤ L.lens∧Tendsto y p' (𝓝 (X r))∧∀ᶠ j in p',readingPrice R d L r (Y r) (m r) (q r) (A₀ r) t (b r) (v r) j (y j)) ∧
        ∀ (Y':ℝ→ Points n),Tendsto Y' home (𝓝 x) → ∀ (f':ℝ→(Fin n→ E4) →ℂ) (N l:ℕ), let c:= fun r=> Z.g r^N*Z.Λ r^l
                                                                                         ; let z:= fun i=> posed i (Y' i)
                                                                                         ; Loom (fun i y=> (c i:ℂ)⁻¹ * f' i y) z →
           (∀ b:ℝ→Fin n → Cover,Tendsto (fun i=> tag (role C i) (b i)) home (𝓝 x) → ∃ (X:ℝ→ R.family.label t), (∀ᶠ r in home, ∃ (p':Filter (ℕ×ℕ))(y:ℕ×ℕ→ R.family.label t),p'.NeBot∧p'≤ L.lens∧Tendsto y p' (𝓝 (X r))∧∀ᶠ j in p',readingPrice R d L r (Y r) (m r) (q r) (A₀ r) t (b r) (v r) j (y j)) ∧ ∃ M:ℝ,∀ᶠ i in home, ‖A (toFrame L t i (S.project t (X i))) - f' i (pix R b i)‖≤ M*c i) →
          ∃ M,∀ᶠ i in home, ‖A (toFrame L t i (P.packet t (z i) (d:=d) (fun j=> master L _ i (v i j)) 0))-f' i (z i)‖ ≤ M*c i:=by
    -- redo rate not dependent P choices
    let α:ℝ:= 1/(32*t+2); have ha:0<α:=by unfold α; positivity
    have he:0<(32:ℝ)*t+2:=by positivity
    have hβ:α<1:=by
         unfold α; have hh: (0:ℝ)≤t:=Nat.cast_nonneg t; exact (div_lt_one he).2 (by linarith only [hh])
    obtain ⟨Y,hY⟩:= found ageLarge R.family.path.levels.fits.mesh ha.le
    obtain ⟨q,a,hq,hA,hW⟩:= buys_words R Z fx W d t Y _ hY hβ j Hb h ho ht
    have hv:GradePrice P d (fun r i=>master L _ r (v r i)) 0:=fun j k=>by
        let z(r):= L.shift (d j) r (v r j); apply (engineeringUpper P L Z.reach W (d j) k z ?_).mono
        · simp
        have hX:=runMount R Z fx; exact RateLE.of_norm_le (f:=fun r=> H (Q r)^i) (((hX.power i).pays ageLarge).mono (by norm_num)) (ht.mono (fun r hr=> (RG12.norm_le_mass ..).trans (hr j)))
    refine ⟨α,Y,q,a,ha,hβ,hY,hq,hA,fun x hx=> ⟨fun b hb=>?_,?_⟩⟩
    · have he:= hW b x hx hb; rw [eventually_iff_exists_mem] at he; obtain ⟨K,hK,hk⟩:=he; choose! y V hv using hk; exact ⟨V, mem_of_superset hK fun r hr=>by obtain ⟨p,hV,hz,hy,hU⟩:=hv r hr; exact ⟨p,y r,hV,hz,hy,hU⟩⟩
    intro X hX f N l c Y' hg hp
    have hΛ(i):1≤Z.Λ i:= Z.above i; have hc(i):0 < c i:= mul_pos (pow_pos (Z.positive _) _) (pow_pos (zero_lt_one.trans_le (hΛ _)) _)
    let u:= fun r=> (c r:ℂ)⁻¹; have h(i) (x:ℂ): ‖u i*x‖= ‖x‖/c i:=by unfold u; rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hc i|>.le),div_eq_mul_inv,mul_comm]
    have hC:RateLE home T u 0:=by
        have he(i): ‖u i‖≤ ((Z.g i)^N)⁻¹:=by nth_rw 1 [← mul_one (u i),h,norm_one]; rw [one_div]; exact inv_anti₀ (pow_pos (Z.positive _) _) (le_mul_of_one_le_right (pow_nonneg (Z.positive _|>.le) _) (one_le_pow₀ (hΛ i)))
        apply ((Z.coarse_g.power N).inv.pays ageLarge).of_norm_le (Eventually.of_forall he)|>.mono
        simp
    obtain ⟨M,hM⟩:= heard_A R W fx hz P d t _ hv A u hC j (fun i y=>u i*f i y) X hx hX Y' rfl hg (fun b hb=> by
         obtain ⟨X,hX,M,hM⟩:=hp b hb
         have he':= beacon R W t hz (yields_reads R Z fx W d t b Y m a X q v hY ha hβ ht hb hx ‹Lookup R m› hA P (hX.mono fun i hi=>by obtain ⟨p,y,hp⟩:=hi; exact ⟨y,p,hp⟩))
         let f'(i):= u i * A (toFrame L t i (P.packet t (pix R b i) (d:=d) (fun j=> master L _ i (v i j)) 0-S.project t (X i)))
         letI:FiniteDimensional ℝ (Free C t):=Module.Finite.trans ℂ _
         have hv:RateLE home T f' (-(1/32)):= ((hC.mul (pay_fixed ageLarge ((A.restrictScalars ℝ).toLinearMap) he')).mono (le_of_eq (by rw [zero_add]; unfold α; field_simp; ring)))
         refine ⟨1+M,?_⟩; filter_upwards [hM,(RateIs.const ageLarge one_pos).outweigh hv (by norm_num) ageLarge] with i hi hh
         unfold f' at hh; rw [map_sub,map_sub,mul_sub] at hh
         refine (norm_sub_le_norm_sub_add_norm_sub _ (u i*A (toFrame L t i (S.project t _))) _).trans (add_le_add hh ?_); rw [← mul_sub,h]; exact (div_le_iff₀ (hc i)).mpr hi)
    refine ⟨M,hM.mono fun i hi=>?_⟩; rw [← mul_sub,h] at hi; exact (div_le_iff₀ (hc i)).mp hi
end YM.RG17
