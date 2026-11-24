import YM.RegulatorIR.Axial.Spurs

/-!
# Flatness W1 is enough for axial symmetry on every horizon
The compact Haar localization pays arbitrary powers of t, **at fixed array**.
Measure-preserving even if the rotation is not a forest symmetry. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f : Side}{G:Gauge}{I:Type}[Fintype I]{U:Hook G I (OEdge f)}
variable (H:Stead (full G f) U)
include H
lemma illuminates (B : spins G f → Prop)(h:∀ p,Flat G f p → ∀ᶠ q in 𝓝 p,B q): ∃ a>0,∀ᶠ t in 𝓝[>] 0,∀ x∈{p | ¬B p},∀ u, a≤ U t x u :=by
 let V(d:ℝ):=Ioo (0:ℝ) d
 suffices hp:∃ a>0,∃ d>0,∀ t∈V d,∀ x∈{p | ¬B p},∀ u,a≤ U t x u from by
    obtain ⟨a,ha,d,hd,hq⟩:=hp; exact ⟨a,ha,(Tested.eventually_small hd).mono hq⟩
 by_contra! he
 let k(i:ℕ):ℝ:= (1+i:ℝ)⁻¹; have hx(i:ℕ):0<k i:=by unfold k; positivity
 choose t ht x hm y hy using fun i : ℕ => he (k i) (hx i) (k i) (hx i)
 have hp:Tendsto k atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
 have h₁:Tendsto t atTop (𝓝 0):=squeeze_zero (fun i=>(ht i).1.le) (fun i=>(ht i).2.le) hp
 have h₂:Tendsto (fun i=>U (t i) (x i) (y i)) atTop (𝓝 0):=squeeze_zero (fun i=> H.nonneg ..) (fun i=> (hy i).le) hp
 obtain ⟨p,_,φ,hφ,hP⟩:= isCompact_univ.tendsto_subseq (fun i=>Set.mem_univ (x i,y i))
 have hq:= H.whereR _ _ _ p.1 p.2 (h₁.comp hφ.tendsto_atTop) (continuous_fst.continuousAt.tendsto.comp hP) (continuous_snd.continuousAt.tendsto.comp hP) (h₂.comp hφ.tendsto_atTop)
 obtain ⟨v,hv⟩:= ((continuous_fst.continuousAt.tendsto.comp hP).eventually (h _ hq.1)).exists; exact hm (φ v) hv

lemma superK (B: spins G f→Prop)(h:∀ p,Flat G f p → ∀ᶠ q in 𝓝 p,B q)(k:ℕ):∃ C:ℝ,0≤C ∧ ∀ᶠ t in 𝓝[>] 0,∀ x:spins G f,¬B x → ‖scan U 1 t x‖≤C*t^k:=by
 obtain ⟨a,ha,hx⟩:= illuminates H B h -- fix
 obtain ⟨C,hC,hP⟩:=bounded_exp ha k; refine ⟨C,hC,?_⟩
 filter_upwards [hx,Tested.eventually_pos] with t ht hs
 have hz:0<t:=hs; intro x hv
 let f:= tilt U 1 t x; let c:= Real.exp (-a/t^2)
 have hi : Integrable (fun _ : RoomK G I=>c) (Chart.physical G I):= integrable_const _
 have hm : ‖scan U 1 t x‖≤ c:=by
    apply le_trans (norm_integral_le_of_norm_le hi ?_) (by simp)
    filter_upwards with i
    have hh := ht x hv i
    simp only [tilt,Pi.one_apply,one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]; apply Real.exp_le_exp.mpr; grw [hh]
 apply hm.trans; apply le_of_mul_le_mul_right (a:=(t⁻¹)^k) _ (by positivity)
 calc
  _ ≤ (1+t⁻¹)^k*Real.exp (-a*(t⁻¹)^2):=by
    rw [mul_comm c, show c=Real.exp (-a*(t⁻¹)^2) from by unfold c;simp [div_eq_mul_inv]]
    gcongr;linarith
  _ ≤ C:= hP _ (by positivity)
  _ = _:=by rw [mul_assoc,← mul_pow,mul_inv_cancel₀ hz.ne',one_pow,mul_one]

-- uniform all U but not cutoff
omit H
def Glows (F: ℝ→ spins G f→ℝ): Prop:=∀ p:Signed,∀ k:ℕ,∃ C:ℝ,0≤C ∧ ∀ᶠ t in 𝓝[>] 0,∀ x, ‖F t (cane p x)-F t x‖≤ C*t^k
omit [Fintype I] in
lemma earth (N:Scale) (h:Even f.val): Glows (G:=G) (f:=f) (scan (startO N) 1):=by
 intro p k; refine ⟨0,le_rfl,Eventually.of_forall fun t x=>?_⟩
 have hh:valueO (cane p x)=valueO x:=by unfold valueO;rw [lifted p x h,energy_pull]
 rw [head,head];unfold tilt startO; rw [hh]; simp

variable (D:StepData c f){F:Forest D.ratio}
variable (N:Scale)(B:D.patch.Branches D.kernel G)(hf:Even f.val)(hc:Even c.val)(hx : Archive G f U 1)
include H hx hf hc B
lemma lantern (G':Glows (scan U 1))(P:Square F) :
 Glows (scan (fuse (dropQ D F G) U (nextO D F N)) (blade _ (dropQ D F G) (1:Hook G I _))) :=by
 intro p e; let Q(u:spins G f):=∀ v:spins G c,bond D (cane p u) (cane p v)=bond D u v
 have hh(u): Flat G f u → ∀ᶠ v in 𝓝 u,Q v:=fun h=>turned p u hf D B h
 obtain ⟨C,hC,h⟩:= superK H Q hh e; obtain ⟨k,hk,h'⟩:= G' p e
 refine ⟨k+ (C+C),by positivity,?_⟩; filter_upwards [h,h',Tested.eventually_pos] with t ht hE hs
 intro v; rw [promoted D N B H (shapeOne (G:=G) (I:=OEdge f) (E:=I)) hx P hc hf,promoted D N B H shapeOne hx P hc hf]
 let g(v:spins G c)(u:spins G f):=scan U 1 t u*pushO D N u t v
 have hG(z:spins G c): Integrable (g z) (Chart.physical G (OEdge f)):= heightBound D N B (H.allows shapeOne) t z
 let M:= caned (G:=G) p hf; have hM: MeasurePreserving M (Chart.physical G _) (Chart.physical G _):= measured p (G:=G)
 let f:= g (cane p v) ∘ M
 have hI: Integrable f (Chart.physical G _):=(hM.integrable_comp_emb M.measurableEmbedding).mpr (hG _)
 rw [← hM.integral_comp' (g (cane p v))]; change ‖(∫ x,f x ∂physical G _) - ∫ x,g v x ∂physical G _‖≤ (k+(C+C))*t^e; rw [← integral_sub hI (hG v)]; refine (norm_integral_le_of_norm_le (integrable_const ((k+(C+C))*t^e)) ?_).trans (by simp)
 filter_upwards with u; let z:=cane p u; let m:= scan U 1 t
 let W:=pushO D N z t (cane p v);let Y:= pushO D N u t v
 change ‖m z*W-m u*Y‖≤ _
 have h₁: ‖(m z-m u)*W‖≤ k*t^e:=by rw [norm_mul];exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (income D N ..)) (hE u)
 have h₂ : ‖m u*(W-Y)‖ ≤ (C+C)*t^e:=by
    have h : 0 < t:= hs -- add eventually
    by_cases he: Q u
    · rw [show W=Y from by unfold W Y pushO; rw [show bond D z (cane p v)= _ from he v],sub_self,mul_zero,norm_zero]; positivity
    rw [norm_mul]; let a:=C*t^e
    have hp: ‖W-Y‖≤ 1+1:= (norm_sub_le ..).trans (add_le_add (income D N ..) (income D N ..))
    exact ((mul_le_mul (ht u he) hp (norm_nonneg _) (by positivity)).trans_eq (by ring))
 rw [show m z*W- m u*Y=(m z-m u)*W +m u*(W-Y) by ring]; exact ((norm_add_le ..).trans (add_le_add h₁ h₂)).trans_eq (by ring)
end YM.RegulatorIR.Axial
