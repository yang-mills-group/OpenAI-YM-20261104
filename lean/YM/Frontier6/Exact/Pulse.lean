import YM.Frontier6.Exact.Hand

/-!
# Covariant recapture packed as CLM on continuous detector samples

Take mirror pair *and* rotation orbit of every hand-detector site. Use actual
true rotations. Complex-linear extraction after averaging. Orbit data can be
formed equally of cluster readings in a detector collar. Compact parameter,
order-zero tests (point/Haar) suffice. Here construction through circ (one
horizon). Nesting separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius ComplexOrder BigOperators Classical
scoped instance : CompactSpace Ortho:= Work.A12.compact_ortho
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) (s:StateIndex K) (p:Probe S) {d n:ℕ}
set_option quotPrecheck false
local notation "R"=> K.sector.turns
local notation "L"=> K.phase.transport.spots
local notation "J"=> S.conj K.room.kernel.spin
private theorem cancel_g (v:Ortho)(x:S.Field d): (R).act d v ((R).act d v⁻¹ x)=x := by rw [← (L).group,mul_inv_cancel,(L).fixes]

/-- Real linear Conjugation clm (used with real Haar integral). -/
def realJ (K:Final C F S)(d:ℕ): S.Field d →L[ℝ] S.Field d:= by
  letI : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _
  refine LinearMap.toContinuousLinearMap { toFun := S.conj K.room.kernel.spin d, map_add' := fun _ _=> map_add .., map_smul' := fun c x=> ?_ }
  rw [show RingHom.id ℝ c=c from rfl,RCLike.real_smul_eq_coe_smul (K:=ℂ) c x,LinearMap.map_smulₛₗ]
  rw [show (starRingEnd ℂ) ↑(algebraMap ℝ ℂ c)=(algebraMap ℝ ℂ c) from by change (star (c:ℂ))=_; simp]
  exact (RCLike.real_smul_eq_coe_smul _ _).symm
@[simp] lemma real_j (d:ℕ)(x:S.Field d): realJ K d x=(J) d x:=rfl

def boost (d:ℕ)(g:Ortho): S.Field d →L[ℂ] S.Field d:= LinearMap.toContinuousLinearMap ((R).act d g).toLinearMap
lemma boost_at (d:ℕ) (v:Ortho) (x:S.Field d): boost K d v x = (R).act d v x:=rfl
lemma boost_cont (d:ℕ): Continuous (boost K d) :=
  continuous_iff_continuousAt.mpr (fun _=> Dash.fit_plane _ _ (fun x=>(L).spin d x|>.continuousAt))
lemma boost_value {X:Type*}[TopologicalSpace X] {v:X→ Ortho}{x:X → S.Field d}(hv:Continuous v)(hx:Continuous x) : Continuous (fun i=> (R).act d (v i) (x i)):=by
  simp_rw [← boost_at]; exact ((boost_cont K d).comp hv).clm_apply hx


def Probe.flip (p:Probe S)(K:Final C F S)(b:Bool): Probe S:= if b then {p with letter:= conjug K ∘ p.letter} else p

def Probe.roll (p:Probe S)(K:Final C F S)(g:Ortho): Probe S:=
  { p with letter:= K.sector.turns.label g ∘ p.letter
           exterior:= Points.move g p.exterior
           clear:=by have he:= Points.move_in g p.clear; rw [rotates_cons,rotates_zero] at he; exact he }
lemma form_twist (g:Ortho) (x:S.Field d) : (p.roll K g).form K s d x=p.form K s d ((R).act d g⁻¹ x):=by
  nth_rw 1 [← cancel_g K g x]; have ht:= read_move K s g 0 p.exterior p.letter ((R).act d g⁻¹ x) p.clear; rw [rotates_zero] at ht; exact ht
lemma form_inv (x:S.Field d): (p.flip K true).form K s d ((J) d x) = star (p.form K s d x):= read_conj K s 0 p.exterior p.letter x p.clear
lemma form_cont (x:S.Field d) : Continuous (fun g=> (p.roll K g).form K s d x):=by simp_rw [form_twist]; exact (p.form K s d).continuous.comp (((L).spin d x).comp continuous_inv)

/-- Sample type for the point/Haar orbit attendance of hand cap `d`. -/
abbrev Hand.Pulse (t:Hand K d) := ↥t.list → Bool → C(Ortho,ℂ)
variable (d) (t:Hand K d)

def Hand.echo {d:ℕ}(t:Hand K d)(e:ℕ) : S.Field e →L[ℂ] t.Pulse:=
  LinearMap.toContinuousLinearMap
    { toFun:=fun x p b=> ⟨fun g=> ((p.val.flip K b).roll K g).form K none e x, form_cont K none _ x⟩
      map_add':=fun x y=> funext fun i=> funext fun b=> ContinuousMap.ext fun g=> (((Probe.roll ((i.val).flip K b) K g)).form K none e).map_add x y
      map_smul':=fun c x=> funext fun i=> funext fun b=> ContinuousMap.ext fun g=> (((Probe.roll ((i.val).flip K b) K g)).form K none e).map_smul c x }

lemma echo_at {e:ℕ}(x:S.Field e)(p:t.list)(b:Bool)(g:Ortho): (t.echo K e x p b g) = ((p.val.flip K b).roll K g).form K none e x:= rfl

local instance borelO : MeasurableSpace Ortho:= borel _
local instance : BorelSpace Ortho:= ⟨rfl⟩
local notation "μ" => (Measure.haar:Measure Ortho)
local notation "Z" => (μ).real univ
private theorem orth_fin : 0 < Z:= by
  have hc: μ univ < ⊤:= measure_lt_top ..
  have ht: 0 < μ univ:= IsOpen.measure_pos (U:=Set.univ) _ isOpen_univ univ_nonempty
  exact ENNReal.toReal_pos ht.ne' hc.ne

-- avg one by g. formula sin(components). `visit` first averages conjugate branches at hand recovery to the unmoved cap.

def visit : ((↥t.list→ℂ) × (↥t.list→ℂ)) →L[ℂ] S.Field d:= by
  refine LinearMap.toContinuousLinearMap {
    toFun x := ((1/2:ℂ) • (t.recover x.1+(J) d (t.recover (star x.2))))
    map_add':= ?_
    map_smul':= ?_ }
  · rintro ⟨x,x'⟩ ⟨y,y'⟩; simp only [Prod.fst_add,Prod.snd_add,star_add,map_add,smul_add]; abel
  · rintro c ⟨x,x'⟩; simp only [Prod.smul_fst,Prod.smul_snd,star_smul, map_smul, LinearMap.map_smulₛₗ]; simp [smul_add, smul_smul,mul_comm]
lemma visit_at (f g:t.list→ℂ): visit K d t (f,g)= (1/2:ℂ) • (t.recover f+(J) d (t.recover (star g))):= rfl
lemma visit_bar (f g:t.list→ℂ): visit K d t (star g,star f)=(J) d (visit K d t (f,g)):=by
  have hu:(starRingEnd ℂ) 2=2:= by rw [show (2:ℂ)=1+1 by ring, map_add,map_one]
  rw [visit_at,visit_at,LinearMap.map_smulₛₗ,map_add,S.reflect_star,show starRingEnd ℂ (1/2:ℂ)=1/2 by rw [map_div₀,map_one,hu]]; simp [add_comm]
lemma visit_exacts (f:t.list→ℂ)(x:S.Field d)(h₁:∀ (p:t.list), p.val.form K none d x = f p) : visit K d t (f, fun p => (p.val.flip K true).form K none d x) = x:=by
  rw [visit_at]; have ht:t.recover f=x:= by convert t.exacts x using 2; exact (funext h₁).symm
  have hp : star (fun p:↥t.list => (p.val.flip K true).form K none d x) =(fun p:↥t.list =>p.val.form K none d ((J) d x)):=by
    ext1 p; change star (_ : ℂ)=_
    nth_rw 1 [← S.reflect_star K.room.kernel.spin d x]; dsimp only; rw [form_inv,star_star]
  rw [ht,hp,t.exacts,S.reflect_star,← two_smul ℂ x,smul_smul]; norm_num

def pulseStep (g:Ortho): t.Pulse →L[ℂ] S.Field d:= by
  let l (b:Bool) : t.Pulse →L[ℂ] (t.list→ℂ):= ContinuousLinearMap.pi (fun p=> (ContinuousMap.evalCLM ℂ g) ∘L ((ContinuousLinearMap.proj («R»:=ℂ) b) ∘L ContinuousLinearMap.proj («R»:=ℂ) p))
  exact boost K d g ∘L (visit K d t) ∘L (l false).prod (l true)
lemma pulse_at (g:Ortho)(f:t.Pulse): pulseStep K d t g f = (R).act d g (visit K d t (fun p=> f p false g, fun p=> f p true g)):=rfl
private lemma pulse_cont (f:t.Pulse) : Continuous (fun g=> pulseStep K d t g f):=by
  simp_rw [pulse_at]; refine boost_value K continuous_id ((visit K d t).continuous.comp (Continuous.prodMk ?_ ?_)) <;> exact continuous_pi (fun p=> (f p _).continuous)
lemma pulse_fin (f:t.Pulse): Integrable (fun g=> pulseStep K d t g f) μ:= (pulse_cont K d t f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma pulse_bound : ∃ (B:ℝ), ∀ (f:t.Pulse) (g:Ortho), ‖pulseStep K d t g f‖ ≤ B* ‖f‖:=by
  have hb: Continuous (fun g=> ‖boost K d g‖):= (show Continuous (fun ZZ : S.Field d →L[ℂ] S.Field d => ‖ZZ‖) from (continuous_norm (E:=S.Field d →L[ℂ] S.Field d))).comp (boost_cont K d)
  obtain ⟨g,hg,hm⟩:= isCompact_univ.exists_isMaxOn univ_nonempty  hb.continuousOn
  refine ⟨‖boost K d g‖*‖visit K d t‖,fun f v=>?_⟩
  let y (b:Bool)(p:↥t.list):ℂ:= f p b v
  have he (b:Bool): ‖y b‖ ≤ ‖f‖:=pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.mpr fun i=> ((f i b).norm_coe_le_norm v).trans ((norm_le_pi_norm (f i) b).trans (norm_le_pi_norm f i))
  rw [mul_assoc]; change ‖boost K d v _‖ ≤ _
  apply ((boost K d v).le_opNorm _).trans; refine mul_le_mul (hm (mem_univ v)) ?_ (norm_nonneg (visit K d t (y false,y true))) (norm_nonneg (boost K d g))
  exact ((visit K d t).le_opNorm _).trans (mul_le_mul_of_nonneg_left (show ‖(y false,y true)‖ ≤ _ from max_le (he false) (he true)) (norm_nonneg (visit K d t)))

private def before (d:ℕ)(t:Hand K d): t.Pulse →ₗ[ℂ] S.Field d:=
  { toFun:= fun f=>∫ g:Ortho, pulseStep K d t g f ∂μ
    map_add':=fun f g=> by simp_rw [map_add]; exact integral_add (pulse_fin K d t f) (pulse_fin K d t g)
    map_smul':=fun c g=> by simp_rw [map_smul]; exact integral_smul .. }
def surround : t.Pulse →L[ℂ] S.Field d:=by
  let b:= pulse_bound K d t; refine (Z)⁻¹ • ((before K d t).mkContinuous ((Z)*b.choose) (fun f=>?_))
  let C:=b.choose*‖f‖; rw [mul_assoc]; change ‖∫ g:Ortho,_ ∂μ‖ ≤ _;
  apply (norm_integral_le_of_norm_le (integrable_const («μ»:=μ) C) (Eventually.of_forall (b.choose_spec f))).trans_eq
  rw [integral_const]; rfl
lemma surround_at (f:t.Pulse): surround K d t f= (Z)⁻¹ • (∫ g:Ortho, pulseStep K d t g f ∂μ):= rfl
lemma surrounds (x:S.Field d): surround K d t (t.echo K d x)=x:=by
  have ht(g): pulseStep K d t g (t.echo K d x)=x:=by
    rw [pulse_at]; simp_rw [echo_at,form_twist, show ∀ (p:Probe S), p.flip K false=p from fun p=> rfl]; rw [visit_exacts K _ t _ ((R).act _ g⁻¹ x) (fun _=> rfl)]; exact cancel_g K g x
  rw [surround_at]; simp_rw [ht]; rw [integral_const]; exact inv_smul_smul₀ orth_fin.ne' _
def leftPulse (u: Ortho)(f:t.Pulse): t.Pulse:=fun p b=> ⟨fun g=> f p b (u⁻¹*g),(f p b).continuous.comp (continuous_const.mul continuous_id)⟩
def flipPulse (f:t.Pulse):t.Pulse:=fun p b=>star (f p (!b))
lemma surround_left (u:Ortho)(f:t.Pulse):
  surround K d t (leftPulse K d t u f)=(R).act d u (surround K d t f):=by
  let T:= (boost K d u).restrictScalars ℝ
  have hv:T= T:= rfl
  have he(g):pulseStep K d t (u*g) (leftPulse K d t u f)= T (pulseStep K d t g f):=by
    rw [pulse_at,pulse_at,(L).group]; refine congr_arg ((R).act _ u) (congr_arg ((R).act _ g) (congr_arg (visit K d t) (Prod.ext ?_ ?_))) <;> ext1 p <;> exact congr_arg (f p _) (inv_mul_cancel_left u g)
  change _ = T _; rw [surround_at,surround_at,map_smul,← T.integral_comp_comm (pulse_fin K d t f),← integral_mul_left_eq_self (fun g=> pulseStep K d t g (leftPulse K d t u f)) u]
  simp_rw [he]
lemma surround_flip (f:t.Pulse): surround K d t (flipPulse K d t f)=(J) d (surround K d t f):=by
  let T:= realJ K d; change _ = T _
  have he(g):pulseStep K d t g (flipPulse K d t f)= T (pulseStep K d t g f):=by
    rw [pulse_at,pulse_at]; change _ = (J) _ _; rw [(L).real]; exact congr_arg ((R).act _ g) (visit_bar K _ t _ _)
  rw [surround_at,surround_at,map_smul,← T.integral_comp_comm (pulse_fin K d t f)]; simp_rw [he]
lemma echo_left (u:Ortho){e:ℕ}(x:S.Field e): leftPulse K d t u (t.echo K e x)= t.echo K e ((R).act e u x):=by
  refine funext fun p=> funext fun b=> ContinuousMap.ext fun g=>?_
  change (t.echo K e x p b (u⁻¹*g))=_; rw [echo_at,echo_at,form_twist,form_twist,← (L).group,mul_inv_rev,inv_inv]
lemma echo_flip {e:ℕ}(x:S.Field e): flipPulse K d t (t.echo K e x) = t.echo K e ((J) e x):=by
  refine funext fun p=> funext fun b=> ContinuousMap.ext fun g=>?_
  change star ((t.echo K e x p (!b) g):ℂ)=_
  let q:=(R).act e g⁻¹ x
  rw [echo_at,echo_at,form_twist,form_twist,← (L).real]
  cases b
  · change star ((p.val.flip K true).form K none e q)= (p.val.form K none e ((J) e q))
    nth_rw 1 [← S.reflect_star K.room.kernel.spin e q];rw [form_inv,star_star]
  exact (form_inv K none _ q).symm
end YM.Frontier6
