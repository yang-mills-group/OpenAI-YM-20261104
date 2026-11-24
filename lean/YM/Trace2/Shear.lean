import YM.Trace2.Orthogonal
import YM.Trace2.Across

/-! Separated shear criterion for the trace. The radiative hypotheses in
this file remain estimates to be made on actual frames. They are NOT inputs
granted by E-existence.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Trace
open Function Set Filter Table Maxwell Labels Climb Work.A01 Next.UVStress UVNext.FreeStress Spin
open Spec OPE Points Analysis
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G} {f:Extraction.Order} {S : Table C.book}

local notation "E"=> (freeTable C.labels)
abbrev Portrayal4 (S:Table C.book):= ℝ→((E).Field 4 ≃ₗ[ℂ] S.Field 4)
variable (F:Final C f S)(P:Portrayal4 S)

def metric0 (F:Frames G) (i j: Axis) := - canonicalStress F i j
structure StressRay (P0 : (E).Field 4 → S.Field 4)(r:ℝ)(a d:ℝ)(k:ℂ) : Prop where
   tensor : ∀ i j : Axis, r^(4:ℕ) • F.sector.energy i j=a • P0 (metric0 _ i j) +
         if i=j then d • P0 (scalarLabel _) + k • S.unit _ else 0
-- In the frame ˇH at μ=1/r, P=ˇH_r. The stress representation includes k times the unit on the diagonal.
structure Rectilinear (P0: (E).Field 4≃ₗ[ℂ] S.Field 4) (r:ℝ) where
   action : (E).Rotation
   derivative : DiffPlan E
   hierarchy : (E).Hierarchy
   tensor : Tensorial action (canonicalStress C.labels)
   laws : action.Laws derivative hierarchy.spin
   oriented : action.Oriented E
   real_align : realH F.room.kernel.spin hierarchy.spin P0
   reproduce (x:Ortho) (q : (E).Field 4) : F.sector.turns.act 4 x (P0 q)= P0 (action.act 4 x q)
   unit : P0 ((E).unit 4)=S.unit 4
lemma ray_of_alignment {r:ℝ} (h : Rectilinear F (P r) r)(hG:G.Simple) : ∃ a b k, StressRay F (P r) r a b k := by
   let A:=(P r).symm; let J(i j:Axis): (E).Field 4:= A (r^(4:ℕ) • F.sector.energy i j)
   let α:=h.action; have hl : Tensorial α J:=by
      intro s i j; have he(q): A (F.sector.turns.act 4 s q)=h.action.act 4 s (A q):= (by simpa [A] using congr_arg A (h.reproduce s (A q)))
      unfold α J
      rw [← he,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,F.phase.transport.spin]
      simp only [Finset.smul_sum,map_sum,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ) (r^4), smul_smul]
      apply Finset.sum_congr rfl;intro i' _;apply Finset.sum_congr rfl
      exact fun j' _=>congr_arg (· • _) (mul_comm ..)
   have hr : ∀ i j:Axis,(E).conj h.hierarchy.spin 4 (J i j)=J i j:=fun i j=> (P r).injective (by
      unfold J A
      rw [h.real_align.2,LinearEquiv.apply_symm_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,F.phase.transport.conserved.real]; simp)
   obtain ⟨a,d,k,hx⟩:=decomposed_stress h.hierarchy h.action h.laws h.oriented h.tensor hG (J:=J) hl (fun i j=> congr_arg (fun v=>(A ((r^4:ℝ) • v))) (F.phase.transport.conserved.symmetric i j)) hr
   refine ⟨-a,d,k,⟨fun i j=>?_⟩⟩
   have hw:=congr_arg (P r) (hx i j); dsimp only [J,A] at hw
   convert hw using 1; · exact (LinearEquiv.apply_symm_apply (P r) _).symm
   simp only [metric0,map_neg,neg_smul,smul_neg,neg_neg,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_add,map_smul,apply_ite,map_zero,h.unit]; split <;> simp_all only [if_true, if_false]

section Computation
def first_value {L:Register G} {S:Table L} (d : ℕ) (x:S.Field d) := S.useAt S 0 (fun _ : Fin 1=> ⟨d,x⟩)
def focus (d:ℕ) (x:S.Field d) := x - first_value d x • S.unit d

def scalarRay (s : ℝ) := P s (scalarLabel _)
def tensorRay (s : ℝ)(i j:Axis) : S.Field 4:= P s (metric0 _ i j)

def custom {e d:ℕ} (x:Points 2)(v:S.Field e)(w:S.Field d) := S.useAt S x (Fin.cons ⟨e,v⟩ (fun _:Fin 1=>⟨d,w⟩))
local notation "κeu"=> custom (S:=S)
set_option backward.isDefEq.respectTransparency false in
lemma custom_linear {e d:ℕ} (x:Points 2)(w:S.Field d) : ∃ L : S.Field e →ₗ[ℂ] ℂ,∀ v, κeu x v w=L v:= by
  let a := Fin.cons (α:=fun _:Fin 2=> ℕ) e (fun _:Fin 1=>d)
  let b v:= (Fin.cons ⟨e,v⟩ (fun _:Fin 1=>⟨d,w⟩) : Fin 2→S.Tag)
  let b'(v:S.Field e)(j) : S.Field (a j) := Fin.cases v (fun _:Fin 1=>w) j
  let L := S.classMoment S a x
  refine ⟨L.toLinearMap (b' 0) 0,fun v=> ?_⟩
  change κeu x v w = L (update (b' 0) 0 v)
  have he : b v=fun j=>⟨_,b' v j⟩ := funext (fun j=>Fin.cases rfl (fun k=>by fin_cases k; rfl) j)
  calc _ = L (b' v) := by change S.useAt S x (b v)=_; rw [he];rfl
       _ = _:= congrArg L (funext (fun j=> Fin.cases (by simp [b']) (fun k=> by fin_cases k; change (w:S.Field d)=(update (b' 0) 0 v) (1:Fin 2); simp [b', show (1:Fin 2)≠0 from by decide]; rfl) j))

def customDer {e d:ℕ} (x:Points 2)(a : Axis)(v:S.Field e)(w:S.Field d):= gradient 0 a (fun x=> κeu x v w) x
local notation "D"=> customDer (S:=S)
lemma customDer_linear {e d:ℕ} (x:Points 2)(w:S.Field d)(a : Axis)(hx : x∈ conf _) (P₀:DiffPlan S) (hP : P₀.Derivatives S) : ∃ L : S.Field e →ₗ[ℂ] ℂ,∀ v, D x a v w=L v:= by
   obtain ⟨L,hL⟩:= custom_linear (e:=e+1) x w
   exact ⟨L.comp (P₀.deriv ..), fun v=> (hP.kernels e a v hx _).symm.trans (hL _)⟩
include F in
lemma custom_derivative_unit {e d:ℕ} (x:Points 2)(w:S.Field d)(a : Axis)(hx:x∈conf _): D x a (S.unit e) w=0:=by
    unfold customDer custom
    let A:=F.sector.derivatives; have hD:=F.phase.transport
    rw [← hD.derivatives.kernels e a (S.unit e) (w:=fun _=>⟨d,w⟩) hx]
    change κeu x ((A.deriv e a) (S.unit _)) w = 0
    rw [A.unit_drop F.room.kernel.laws hD.derivatives F.room.kernel.smooth e a]
    
    obtain ⟨L,hL⟩:=custom_linear (e:=e+1) x w; rw [hL,L.map_zero]
lemma conservation_pairs {d:ℕ} (w:S.Field d)(b : Axis) (x:Points 2)(hx :x∈conf _)(r:ℝ) : ∑ a:Axis, D x a (r^(4:ℕ) • F.sector.energy a b) w=0:= by
   let A:=F.sector; have h:= F.phase.transport
   have he a : D x a (r^(4:ℕ) • A.energy a b) w=(↑(r^4:ℝ):ℂ) • κeu x (A.derivatives.deriv 4 a (A.energy a b)) w:= by
      obtain ⟨L,hL⟩:= customDer_linear x w a hx A.derivatives h.derivatives
      rw [hL, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,← hL]; apply congr_arg; exact (h.derivatives.kernels (B:=(A.energy a b)) (w:=fun _=>⟨d,w⟩) _ a (hx:=hx)).symm
   obtain ⟨L,hL⟩:=custom_linear (e:=5) x w
   simp_rw [←show A.energy=F.sector.energy from rfl,he,hL,←Finset.smul_sum,← map_sum]
   rw [h.conserved.divergence b,L.map_zero,smul_zero]

theorem divergence_system {r a d p} (hr:StressRay F (P r) r a d p){k:ℕ} (v : S.Field k)
    (y:Points 2)(hy:y∈conf _)(b:Axis) :
    (a:ℝ) • (r • ∑ i:Axis, D y i (tensorRay P r i b) v) + (d:ℝ) • (r • D y b (scalarRay P r) v) = 0:=by
    have he:=congr_arg (r • ·) (conservation_pairs F v b y hy r)
    rw [Finset.smul_sum,smul_zero] at he
    choose L hL using fun i:Axis=> customDer_linear (e:=4) y v i hy F.sector.derivatives F.phase.transport.derivatives
    have hL' (k i) (q:S.Field 4): L i (k•q)= (k:ℝ) • L i q:= ((L i).restrictScalars ℝ).map_smul ..
    let J i j := tensorRay P r i j; let T:=scalarRay P r
    have hv i : D y i (r^4 • F.sector.energy i b) v=a • D y i (J i b) v+ if i=b then d • D y b T v else (0:ℂ):=by
       rw [hL,hr.tensor,map_add,hL']; rw [apply_ite (L i)]; simp only [map_add,hL',map_smul,map_zero];simp only [← hL]; split
       · rename_i hx;subst i; rw [custom_derivative_unit F y v b hy,smul_zero,add_zero]; rfl
       rfl
    simp_rw [hv] at he
    rw [← Finset.smul_sum, Finset.sum_add_distrib,← Finset.smul_sum] at he
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    rw [smul_comm a r,smul_comm d r,← smul_add]; exact he
def anomalyCoefficient (G : Gauge):ℝ:=11*G.casimir/(48*Real.pi^2)
def theoryDensity (G : Gauge):ℝ:=3*G.lieDim/Real.pi^4
lemma anomalyCoefficient_pos (h:G.Simple):0<anomalyCoefficient G:=by unfold anomalyCoefficient; positivity [Gauge.casimir_pos h]
lemma theoryDensity_pos (h:G.Simple):0<theoryDensity G:=by dsimp only [theoryDensity];
                                                           have hn : 0 < G.lieDim := by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos
                                                           positivity

local notation "home" => (𝓝[>] (0:ℝ))
open Complex

def βdiag (r) := r • D (separated r) timeAxis (scalarRay P r) (focus 4 (scalarRay P r))
def σdiag (r) := r • ∑ i : Axis, D (separated r) i (tensorRay P r i timeAxis) (focus 4 (scalarRay P r))
def Kdiag (r) := κeu (separated r) (focus 4 (scalarRay P r)) (focus 4 (scalarRay P r))

/-- Needed leading Ward channel and scalar/shear matching data on SAME unselected law. The `g²`
through the mixed two-point derivative is a quantitative, not leading Wick, comparison. Conditional
on true Wilson estimates; constant shifts cancel. Inverse-length variable r⁻¹. -/
structure ShearRead (filt : Filter ℝ) (g a d : ℝ→ℝ) (k : ℝ→ℂ) : Prop where
   rays : ∀ᶠ r in filt, StressRay F (P r) r (a r) (d r) (k r)
   translates : Tendsto a filt (𝓝 1)
   derivative : Tendsto (βdiag P) filt (𝓝 (↑(8*theoryDensity G):ℂ))
   leading : Tendsto (Kdiag P) filt (𝓝 (↑(theoryDensity G):ℂ))
   radiative : Tendsto (fun r=> σdiag P r/↑(g r)^2) filt
                 (𝓝 ((↑(4*anomalyCoefficient G * theoryDensity G):ℂ)))

variable {filt:Filter ℝ} {g a d:ℝ→ℝ}{k:ℝ→ℂ}
include F P in
lemma d_comparison (H : ShearRead F P filt g a d k)(h:G.Simple)(hg : ∀ᶠ r in filt, 0<g r ∧ 0<r) : Tendsto
   (fun r=>d r/(g r)^2) filt (𝓝 (-anomalyCoefficient G/2)):=by
    have ht:= (((continuous_ofReal.continuousAt.tendsto.comp H.translates).mul H.radiative).neg.div H.derivative (by exact_mod_cast (show (8:ℝ)*theoryDensity G≠0 by positivity [theoryDensity_pos h])))
    have hh : Tendsto (fun r=> -(↑(a r)*(σdiag P r/↑(g r)^2 : ℂ))/βdiag P r) filt (𝓝 (-(↑(anomalyCoefficient G):ℂ)/2)):= by
       simp only [ofReal_one,one_mul, Pi.div_def, Function.comp_def] at ht
       convert ht using 2;  push_cast; field_simp [show (↑(theoryDensity G):ℂ)≠0 by exact_mod_cast (theoryDensity_pos h).ne']; ring
    have hr : Tendsto (reCLM ∘ fun r=> -(↑(a r)*(σdiag P r/↑(g r)^2 : ℂ))/βdiag P r) filt (𝓝 (-anomalyCoefficient G/2)) := by
       simpa using reCLM.continuous.continuousAt.tendsto.comp hh
    apply hr.congr'
    filter_upwards [H.rays, H.derivative.eventually_ne (b₂:=0) (by exact_mod_cast (show (8:ℝ)*theoryDensity G≠0 by positivity [theoryDensity_pos h])),hg] with r hr he hp
    have hu:= divergence_system F P hr (focus 4 (scalarRay P r)) (separated r) (room_conf _ _ _ _ _ (room_separated _ hp.2.le) hp.2 one_pos) timeAxis
    change a r • σdiag P r+d r • βdiag P r=0 at hu
    simp only [real_smul] at hu
    simp only [Function.comp_apply]
    suffices hu' : -(↑(a r)*(σdiag P r/↑(g r)^2 : ℂ))/βdiag P r=↑(d r / (g r)^2 : ℝ) by rw [hu'];rfl
    have hX : (↑(g r):ℂ)≠0:=ofReal_ne_zero.mpr hp.1.ne'
    calc _ = - (↑(a r)* σdiag P r)/(↑(g r)^2*βdiag P r) := by ring
         _ = (↑(d r)* βdiag P r)/(↑(g r)^2*βdiag P r) := congrArg (fun x:ℂ=>x/_) (neg_eq_iff_add_eq_zero.mpr hu)
         _ = _ := by push_cast; field_simp
lemma focus_eq (x:S.Field 4) : focus 4 x=centering S 4 x:= by
    unfold focus first_value; rw [value_center, expectation,front_eval]; congr 3
    funext i;fin_cases i;rfl
include F in
lemma trace_ray {r a d p} (hr:StressRay F (P r) r a d p):
   r^4 • focus (S:=S) 4 (theta F 0)=(4*d) • focus 4 (scalarRay P r):= by
   rw [focus_eq,focus_eq]
   let L:=centering S 4; let T:=canonicalStress C.labels
   have hz : ∑ i:Axis,T i i=0:= by simpa [T,torch,one_smul] using torch_traceless C.labels 1
   have hT : (theta F 0)= ∑ i:Axis,F.sector.energy i i:=by unfold theta withoutMean; simp
   have hg (q:S.Field 4)(x:ℝ):L (x • q)=x • L q:= (L.restrictScalars ℝ).map_smul ..
   simp_rw [hT, map_sum, Finset.smul_sum]
   change (∑ i:Axis,r^4 • L (F.sector.energy i i))= (4*d) • L (scalarRay P r)
   have hB(i:Axis) : r^4 • F.sector.energy i i = a • P r (metric0 _ i i) + d • scalarRay P r + p • S.unit 4:= (hr.tensor i i).trans (by rw [if_pos rfl]; exact add_assoc .. |>.symm)
   simp_rw [← hg, hB, map_add,map_smul, show L (S.unit _)=0 from const_out F.room.kernel.laws,smul_zero,add_zero,hg,Finset.sum_add_distrib]
   rw [← Finset.smul_sum,← map_sum,← map_sum, show ∑ x:Axis,metric0 _ x x=0 from by simpa only [metric0,Finset.sum_neg_distrib, ← show ∀ i:Axis,∀ j,T i j=canonicalStress C.labels i j from fun _ _=>rfl, eq_comm (a:=0),neg_eq_zero] using hz ,map_zero,map_zero,smul_zero,zero_add]
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
   rw [← Nat.cast_smul_eq_nsmul ℝ, show (↑(4:ℕ):ℝ)=4 by norm_num]; unfold scalarRay; module
lemma trace_ray_eval {r a d p} (hr:StressRay F (P r) r a d p){x:Points 2} :
   (r^8:ℝ) • κeu x (focus 4 (theta F 0)) (focus 4 (theta F 0))=(4*d)^2 • κeu x (focus 4 (scalarRay P r)) (focus 4 (scalarRay P r)) := by
   have hK (u:ℝ)(v:S.Field 4) : (u^2 • κeu x v v)=κeu x (u • v) (u • v) := by
      have he (v:S.Field 4): Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨4,v⟩ (fun _=>⟨4,v⟩) = (fun i=>⟨4,v⟩):= by funext i; fin_cases i <;> rfl
      unfold custom; rw [he,he]; unfold useAt
      simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),MultilinearMap.map_smul_univ,Fin.prod_univ_two]; congr 1; norm_num [pow_two]
   simp_rw [show (r^8 :ℝ)=(r^4)^ (2:ℕ) by ring]; rw [hK,hK,trace_ray F P hr]
lemma raw_focus_exact (x : Points 2): central F none x= κeu x (focus 4 (theta F 0)) (focus 4 (theta F 0)) := by
    rw [central,traceEta,massCenter_eq]
    have he (v:S.Field 4): Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨4,v⟩ (fun _=>⟨4,v⟩) = (fun i=>⟨4,v⟩):= by funext i; fin_cases i <;> rfl
    unfold custom; rw [he]
    let u:=focus 4 (theta F 0)
    change S.classMoment S (fun _=>4) x ![u,u]=S.classMoment S (fun _=>4) x (fun _=>u)
    congr 1; funext i;fin_cases i <;> rfl

/-- Actual consequence of the UV mixed two-point estimates, at the full continuous scale and
on every phase by the common coefficient prescription (for the same `Final`). In particular
`d_comparison` identifies the ratio for the actual stress. -/
theorem anomaly_heat (H:ShearRead F P home g a d k) (h : Services C f S)
    (hg:Tendsto (fun r:ℝ=>g r ^ (2:ℕ)*Real.log (r⁻¹)) home (𝓝 ((2*anomalyCoefficient G)⁻¹))) (hp:∀ᶠ r in home, g r>0):
     LogLaw F (theoryDensity G) := by
    let K(r):=Kdiag P r
    let q : ℝ:=anomalyCoefficient G
    let M := theoryDensity G
    have hq := d_comparison F P H h.simpleGate (hp.and self_mem_nhdsWithin)
    have hh:= ((Complex.continuous_ofReal.continuousAt.tendsto).comp (((hq.const_mul 4).mul hg).pow 2)).mul H.leading
    let f(r:ℝ) := r^(8:ℕ)*Real.log (r⁻¹)^2
    let c i r := central F i (separated r)
    have hf : Tendsto (fun r=> f r • c none r) home (𝓝 (↑M:ℂ)):= by
       have ht:= (anomalyCoefficient_pos h.simpleGate).ne'
       change Tendsto _ _ (𝓝 (↑((4*(-q/2)*(2*q)⁻¹)^2:ℝ) * ↑M:ℂ)) at hh -- fix type
       have ht' : (4*(-q/2)*(2*q)⁻¹)^2=(1:ℝ) := by field_simp [show q≠0 from ht];ring
       rw [ht',ofReal_one,one_mul] at hh
       apply hh.congr'; filter_upwards [H.rays,hp] with r hr hn

       change ↑(((4*(d r/(g r)^2:ℝ))*((g r)^2 * Real.log r⁻¹))^(2:ℕ):ℝ)*(K r)=_
       rw [show c none r= _ from raw_focus_exact F _] -- c local
       rw [show ((4*(d r/(g r)^2))*((g r)^2 * Real.log r⁻¹):ℝ)=(4*d r)*Real.log r⁻¹ by field_simp [show g r≠0 from ne_of_gt hn]]
       unfold f; rw [mul_comm (r^8:ℝ) (Real.log r⁻¹^2), mul_smul,trace_ray_eval F P hr]; simp only [Complex.real_smul,mul_pow]; unfold K Kdiag; push_cast; ring
    let i:= (some F.α.atPoint : Viewers F)
    have ho : Tendsto (fun r=> f r • (c i r-c none r)) home (𝓝 0) := by
       apply Metric.tendsto_nhds.mpr; intro b hb; filter_upwards [log_agreement F h 1 1 b hb zero_le_one zero_lt_one, (self_mem_nhdsWithin : ∀ᶠ r:ℝ in home,0<r)] with r hr hx
       rw [dist_zero_right]; exact hr _ _ (room_separated _ hx.le) i none
    have hT := ho.add hf; rw [zero_add] at hT
    unfold LogLaw; apply (hT.comp tendsto_inv_atTop_nhdsGT_zero).congr; intro x
    change f (x⁻¹) • (c i (x⁻¹)-_)+_= _
    rw [smul_sub, sub_add_cancel];unfold c logWeight f; rw [inv_inv,Complex.real_smul, restTrace_origin]
end Computation
end YM.Trace
