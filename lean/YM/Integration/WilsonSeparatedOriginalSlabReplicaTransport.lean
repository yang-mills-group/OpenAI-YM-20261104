import YM.Integration.WilsonSeparatedOriginalSlabReplicaAddresses
import YM.Integration.WilsonSeparatedOriginalSlabChildWords
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaTransport
open Function Finset Matrix MeasureTheory Lattice RG Wilson RG05Readout Source Address Push Local Marker MergeProof
open RG05Readout.Flatten RG05Readout.Native RG05Readout.View RG05Readout.Pulse
open Extra.Histories PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open RG05Readout.Pulse RG05Readout.Flatten
open private row from YM.Integration.WilsonSeparatedOriginalSlabChildWords
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{b N p:ℕ}
local notation "V"=>Fin 3
local notation "X!"=>C.side N p
local notation "Y!"=>C.side b p
local notation "Fields"=>V → Config G (C.side N p)
private def shift (q:Site X!)(F:Fields→ℂ):Fields→ℂ:=fun W=>F (fun i=>pull 1 q (W i))
private theorem shiftSum {T:Type*}[Fintype T](q:Site X!)(F:T → Fields → ℂ):
    shift (C:=C) (N:=N) (p:=p) q (∑i,F i)=∑i,shift (C:=C) (N:=N) (p:=p) q (F i):=by
  funext W;simp [shift]
private theorem shiftSmul (q:Site X!)(a:ℂ)(F:Fields→ℂ):shift (C:=C) (N:=N) (p:=p) q (a • F)=a • shift (C:=C) (N:=N) (p:=p) q F:=rfl

def multi (C:Family G)(m N p:ℕ)(s:V→ℕ)(v:(i:V)→ Palette C (s i)):
    Wave V →ₗ[ℂ] ((V→ Config G (C.side N p)) → ℂ):=
  (∏i:V,gate C m N (s i)) • ∑t:V→Site (C.side N p),WilsonSeparatedOriginalReplicaWave.harpoon s v t ∘ₗ fork (C.S.a N) (fun i=>C.S.place (t i))
variable (s:V→ℕ)(v:(i:V)→Palette C (s i))
private theorem continuousFee (y:V→Site X!){E:Type*}[TopologicalSpace E](f:Wave V)(r:ℝ){τ:E→ Cloud V}(hT:Continuous τ)(U:Fields):
    Continuous (fun i=>WilsonSeparatedOriginalReplicaWave.harpoon s v y (fork r (τ i) f) U):=by
    let L:= Finset.univ (α:=V) |>.toList
    have he (j:(i:V)→Mark C (s i)): let a:=(fun i=>(j i).1); Continuous (fun i:E=> (Pulse.perform _ a (fork r (τ i) f)).val 0):=by
       intro a; unfold Pulse.perform; simp_rw [machine_roll]; change Continuous (fun i:E=> (↑r:ℂ)^ _ • (machine s a L f).val (τ i+r • 0)); simp_rw [smul_zero,add_zero]; exact (((lit (machine s a L f) 0).continuous.comp hT).const_smul ((r:ℂ) ^ pegs s a L))
    exact continuous_finsetSum _ (fun i _=> (he i).mul continuous_const)

variable (q:ℝ)(f:Wave V)
local notation "H"=>multi C _ N p s v
theorem whereat (m:ℕ)(z:E4) : (multi C m N p s v) (rel q f z)=(∏i:V,gate C m N (s i)) • ∑ w:V→Site X!,WilsonSeparatedOriginalReplicaWave.harpoon s v w (cameo C p N q f z w):=by
  unfold multi;simp_rw [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,Pulse.rel_taken]
theorem continuous (m:ℕ)(U:Fields):Continuous (fun z:E4=>multi C m N p s v (rel q f z) U):=by
  simp_rw [whereat,Pi.smul_apply,Finset.sum_apply]
  refine Continuous.const_smul (g:=fun z:E4=>∑t:V→Site X!,WilsonSeparatedOriginalReplicaWave.harpoon s v t (cameo C p N q f z t) U) ?_ (∏i:V,gate C m N (s i))
  apply continuous_finsetSum;intro t _;unfold cameo;refine continuousFee s v t f _ (continuous_pi (fun i=>?_)) U;fun_prop

variable (h:b ≤ N)
local notation "r"=>C.S.toDepth h p
local notation "T"=>Site (r).count
local notation "mark"=>fun w:V→Site X!=>WilsonSeparatedOriginalReplicaWave.harpoon (C:=C) (p:=p) (N:=N) s v w
local notation "Y"=>WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v
variable {B R:ℝ}(hq:0<q)(hΨ:∀x∈tsupport f.val,∀i:V,‖x i‖≤R)(hp:q*R+2*C.S.a b<C.S.radius p)(hρ:B+q*R<C.S.radius p)
include hΨ hq hp hρ
theorem original (m:ℕ)(z:Site Y!)(τ:E4)(ht:τ∈Native.box)(he:‖voyager C p b z τ‖≤ B):
    let y:=voyager C p b z τ
    multi C m N p s v (rel q f y)=(∏i:V,gate C m b (s i)) • ∑o:V→Site Y!,shift (C:=C) (p:=p) (N:=N) ((r).embed z) (Y o h (cropX f o q τ)):=by
    intro y; let K:= walks h («V»:=Fin 3) z; rw [whereat,← Equiv.sum_comp K, Fintype.sum_prod_type]; simp_rw [money (C:=C) (p:=p) h,Finset.prod_mul_distrib,mul_smul,Finset.smul_sum]; refine sum_congr rfl fun o _=> ?_;
    unfold WilsonSeparatedOriginalReplicaWave.scalp; rw [LinearMap.sum_apply,shiftSum,Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; rw [LinearMap.smul_apply,shiftSmul]; let t:=fun j:V=> (r).assemble (o j,i j); let u':=K (o,i); let d':=(r).embed z; have hw: (fun i=> t i+d')=u':=by
        funext i'; unfold u' K; change (r).assemble _+d'=(r).assemble (_, i i'); unfold Ratio.assemble;rw [show (r).embed (_+_)=_ from (r).root.map_add (o i') z]; rw [Ratio.root_embed,Ratio.root_embed,add_right_comm]
    let Z:=fork ((↑(r).count.val:ℝ)⁻¹) (fun j=>placeR (r) (i j)) (cropX f o q τ); change _=(∏ x,gate C m b (s x)) • ((∏ i:V, ratioX (r) (s i)) • shift (C:=C) (p:=p) (N:=N) d' (mark t Z)); rw [show shift (C:=C) (p:=p) (N:=N) d' (mark t Z)=mark u' Z from (funext (row s v t d' Z)).trans (by rw [hw])] -- maybe
    apply congr_arg ((∏ i:V, gate C m b (s i)) • ·);apply congr_arg ((∏ i:V,ratioX (r) (s i)) • ·); exact (WilsonSeparatedOriginalSlabReplicaAddresses.original h s v f o q hq hΨ z τ ht he i hp hρ).symm

end YM.Integration.WilsonSeparatedOriginalSlabReplicaTransport
