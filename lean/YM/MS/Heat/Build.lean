import YM.MS.Heat.Signal
/-!
# Euclidean or meshed cycle: line theory, assertion of Elements

No kernel estimates required in abstract except elementary integrability of specified
 terms at a fixed scale. Need gradient proof separately. (Unused arguments if by definitional
 reduction linear selectors.) -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve Base
open scoped Topology ContDiff
variable {P I A:Type} [MeasurableSpace P] [AddCommGroup P][Fintype A]{p: Sector A}{K L: Flux A P ℂ}{Q: Charge p P ℂ} {F H:Row A P ℂ}(μ:Measure P){q:P}
-- bronds: restriction to Pass, extension allowed to arbitrary raw. never read charge of gap.
lemma reconstruction (K:Flux A P ℂ): ∃ L:Op (Mode A P) ℂ,∀ F,Pass K F μ→ L F=Ccy K F μ:= by
    let X:Submodule ℂ (Row A P ℂ):={
        carrier:=setOf (fun F=>Pass K F μ)
        zero_mem':= fun w=>by simp only [map_zero,Pi.zero_apply]; exact integrable_zero ..
        add_mem' {_ _} hv hm:= t_add μ hv hm
        smul_mem' _ _ hv:= cc_scale μ _ hv }
    let L : X →ₗ[ℂ] Row A P ℂ:={
       toFun F:= Ccy K F.val μ
       map_add' F H:= cc_add μ F.property H.property
       map_smul' c F:= ccy_s μ c }
    obtain ⟨T,ht⟩:=Submodule.exists_isCompl X; refine ⟨L.comp (X.projectionOnto T ht),fun F hp=>?_⟩
    let v:X:=⟨F,hp⟩; change L (X.projectionOnto T ht (v.val))=_; rw [Submodule.projectionOnto_apply_left]; rfl

def orbit (K:Flux A P ℂ)(μ:Measure P) : Op (Mode A P) ℂ:= (reconstruction μ K).choose
lemma finite_cc (h:Pass K F μ): orbit K μ F=Ccy K F μ:= (reconstruction μ K).choose_spec F h
-- tree linear and line
omit [MeasurableSpace P] in
lemma r_hmul {X:Type} (v:(X→ℂ)→ℂ)(h:v∈Centre X){a:ℂ}{F:X→ℂ}: v (a • F)=a * v F:=by
   refine Submodule.span_induction (p:=fun v _=> v (a • F)=a*v F) ?_ (by simp) ?_ ?_ h; rintro u ⟨i,rfl⟩; rfl
   · intro v w Hv Hw hi he; simp [hi,he,mul_add]
   intro v u hx ht; simp [ht,mul_left_comm v]
lemma fromCent {X:Type} (p:(X→ℂ)→ℂ)(h:p∈Centre X)(f g:X→ℂ): p (f+g)=p f+p g:=by
   refine Submodule.span_induction (p:=fun v _=> v (f+g)=v f+v g) ?_ (by simp) ?_ ?_ h
   · rintro v ⟨i,rfl⟩; rfl
   · intro v w Hv Hw hi he; simp [hi,he]; ring
   intro v u hx ht; simp [ht,mul_add]
-- from rMap simpler

def boulevard (p:Sector A)(K:Flux A P ℂ): Signal.Pair (Row A P ℂ) where
    toFun F:= { toFun:= tree p K F, map_add':= fun i j=> funext fun k=>fromCent _ ((sense_atRight K F).reaches k) i j, map_smul':=fun _ _=> funext fun k=> r_hmul _ ((sense_atRight K F).reaches k) }
    map_add' F G:= LinearMap.ext (fun H => funext fun i => fromCent (fun F=>tree p K F H i) ((sense_atLeft K H).reaches i) F G)
    map_smul' _ _:= LinearMap.ext (fun H=> funext fun i=> r_hmul _ (sense_atLeft (p:=p) K H|>.reaches i))
omit [MeasurableSpace P] in
lemma blvd (p:Sector A)(K:Flux A P ℂ)(F H: Row A P ℂ): boulevard p K F H= tree p K F H:=rfl

def rack (K L:Flux A P ℂ) (Q:Charge p P ℂ)(μ:Measure P): Signal.GridR (Row A P ℂ):= ⟨Q.raise+orbit L μ, orbit K μ, orbit (Q.change K) μ,boulevard p K,boulevard p L,boulevard p (Q.change K)⟩
local notation "J"=> orbit L μ
local notation "X"=> orbit K μ
structure Pieces0 (K L:Flux A P ℂ)(Q:Charge p P ℂ)(μ:Measure P)(F:Row A P ℂ): Prop where
    K0: Pass K F μ
    L0: Pass L F μ
    K1: Pass K (orbit L μ F) μ -- hygiene K variables? L inside syntax local notation expands variable outer: trouble. replace later
    L1: Pass L (orbit K μ F) μ
    HQ: Pass K (Q.raise F) μ
    shape: Pass (Q.change K) F μ
    double (u:Legs (Mode A P)): Integrable (fun x:P×P=>trc L x.1 (trc K x.2 F) u) (μ.prod μ)
    sym : Symm (field p) F
structure Pieces (K L:Flux A P ℂ)(Q:Charge p P ℂ)(μ:Measure P)(F H:T (Row A P ℂ)): Prop where
    left (n:ℕ): Pieces0 K L Q μ (F n)
    right (n:ℕ): Pieces0 K L Q μ (H n)
    vital : ∀ n, Pure (field p) false (F n)
    K1 n m: Pass L (tree p K (F n) (H m)) μ
    L1 n m: Pass K (tree p L (F n) (H m)) μ
    front n m: Route K L p (F n) (H m) μ
    post n m: Route L K p (F n) (H m) μ
    ck : closed K p false
    cl : closed L p true
    cq : closed (Q.change K) p true
    rk : Reverse K p
    rl : Reverse L p
-- use at any projections
variable {F H: T (Row A P ℂ)}
open Signal
lemma elementary [SigmaFinite μ](h:Pieces K L Q μ F H){E:Type*}[AddCommGroup E][Module ℂ E] (κ:(Row A P ℂ)→ₗ[ℂ] E): GridR.Elements κ (rack K L Q μ) F H:= by
   refine ⟨fun i=>?_ , fun i j=>?_,fun i j k=>congr_arg κ (axis_press h.ck h.cl (h.left i).sym (h.vital i) (h.left j).sym (h.vital j) (h.right k).sym)⟩
   · have Hx:=h.right i; let Hi:= H i; have hh : (Q.raise+J) (X Hi) + orbit (Q.change K) μ Hi=X ((Q.raise+J) Hi):= by
         simp only [LinearMap.add_apply, map_add]; rw [finite_cc μ Hx.L1, finite_cc μ Hx.K1, finite_cc μ Hx.HQ, finite_cc μ Hx.shape, finite_cc μ Hx.K0, finite_cc μ Hx.L0]; rw [comm_T μ h.ck h.cl Hx.K0 Hx.L0 Hx.sym Hx.double,add_right_comm, comm_Q μ Q Hx.K0 Hx.shape h.ck]
     exact congr_arg κ hh
   let f:= F i; let g:=H j; obtain hv:= h.left i; obtain ht:= h.right j
   change κ (((Q.raise+J) (boulevard p K f g)) + boulevard p (Q.change K) f g + boulevard p L (X f) g + boulevard p L f (X g))=κ (X (boulevard p L f g) +boulevard p K ((Q.raise+J) f) g+boulevard p K f ((Q.raise+J) g))
   apply congr_arg κ; simp only [LinearMap.add_apply, map_add]; simp_rw [blvd]; rw [finite_cc μ (h.K1 i j), finite_cc μ (h.L1 i j),finite_cc μ hv.K0,finite_cc μ ht.K0,finite_cc μ hv.L0,finite_cc μ ht.L0]; linear_combination (norm:=abel) axis_level h.ck h.cq ht.sym (h.vital i) hv.sym + exchange_term μ hv.L0 ht.L0 hv.K0 ht.K0 (h.front i j) (h.post i j) h.rl h.rk hv.sym ht.sym (h.vital i) h.ck h.cl
-- as appropriate to kernel read

def point (L:Legs (Mode A P)): Row A P ℂ→ₗ[ℂ] ℂ:= LinearMap.proj L
-- caveat Route made `structure` Type so Pieces not Prop? edit previous.
end YM.MS.Heat
