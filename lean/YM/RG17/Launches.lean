import YM.RG17.Paces
import YM.RG17.Tarmac
import YM.RG17.Avenue
import YM.OPE.Cards.Scale
/-!
# Selected POINT deployments compatible with allClear.

 Sampling in peg coordinates (real r), may perturb x along it. Generic
 required. Price for sensor along pegs on THIS orbit. No claim of Fourier
 content. Real estimate on output, not toe at renormalized reset. In
 particular error not including any wanted WilsonX terms herein.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Finset Spec Lattice Wilson Next.UVStress MergeProof PhysicalNext.Repeat.Legato
open OPE OPE.Orbits MeasureTheory RG Next.Rank Extraction Cells Marker SharpGram
open scoped Topology Classical BigOperators
variable {G:Gauge}
set_option quotPrecheck false
section space
variable {C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}{L:Layout F} {n:ℕ}(W:Ledger L)(fx:Flick C.path.levels) {r:ℝ}{x:Points n}
local notation "θ"=> role C
local notation "K"=> wheel C
local notation "a"=> C.S.a
lemma scaledRole (hr:0<r)(b:Fin n → Cover): r • tag (role C r) b= tag (C.S.a (K r)) b:=by
     ext i j; change r*((_/r)*_)= _; field_simp; rfl -- maybe needs push
include W fx
lemma launches {p:Filter ℝ}(hp:p≤home){b:ℝ→ Fin n → Cover}(h:Tendsto (fun r=>tag (θ r) (b r)) p (𝓝 x))(ht:x∈generic n): ∀ᶠ r in p, tag (a (K r)) (b r)∈generic n ∧
    ∀ᶠ u: ℕ×ℕ in L.lens, let B:=(C.path.levels.budget (wheel C r)).B; Pairwise (fun i j=> B^2 ≤ separation (wrap (C.side (K r) u.2) (b r i)) (wrap _ (b r j))):=by
   let t(j k:Fin n)(r:ℝ):=‖tag (θ r) (b r) j-tag (θ r) (b r) k‖
   let M(r):=(C.path.levels.budget (K r)).B
   have hx:∀ᶠ r in p, Pairwise (fun j k:Fin n=>2*(θ r*(↑(M r):ℝ)^2) ≤ t j k r):=by
        refine eventually_all.mpr fun i=> eventually_all.mpr fun j=>?_ ; by_cases he:i=j; exact Eventually.of_forall fun _ h=> (h he).elim
        have hV:0< ‖x i-x j‖:= norm_sub_pos_iff.mpr ((generic_conf _ ht).ne he)
        have hh: Tendsto (t i j) p (𝓝 ‖x i-x j‖):=ContinuousAt.tendsto (f:=fun x:Points n=> ‖x i-x j‖) (by fun_prop) |>.comp h
        obtain ⟨c,hc,hQ⟩:=exists_between hV; filter_upwards [((bendsPrice W fx).mono_left hp|>.const_mul 2).eventually (gt_mem_nhds (show 2*(0:ℝ)< c from by simpa only [mul_zero] using hc)),hh.eventually (lt_mem_nhds hQ)] with x hx hy _
        exact (hx.trans hy).le
   filter_upwards [positiveLength.filter_mono hp,hx,h.eventually ((genericOpen _).mem_nhds ht)] with r hr hx hR
   rw [← scaledRole hr]
   constructor
   · intro i k j he; apply hR i; exact mul_left_cancel₀ hr.ne' (show r*_ = r*_ from he)
   filter_upwards [(late_period ((eventually_all.mpr fun i=> eventually_all.mpr fun j=> (Cards.native_space (k:=K r) C (b r i) (b r j))) : ∀ᶠ z:ℕ in atTop, ∀ (i j:Fin n), _ ) : ∀ᶠ i in f.fuse, _).filter_mono L.certified] with u hu B i j hij -- fix
   let J:= separation (wrap (C.side (K r) u.2) (b r i)) (wrap _ (b r j))
   have he: ‖tag (a (K r)) (b r) i - tag (a (K r)) (b r) j‖ ≤ 2*(a (K r)*J):= hu i j
   rw [← scaledRole hr,PiLp.smul_apply, PiLp.smul_apply,← smul_sub,norm_smul,Real.norm_of_nonneg hr.le] at he
   have hh: 2*(a (K r)* (↑((M r)^2):ℝ)) ≤ 2*(a (K r)*(J:ℝ)):=by
        refine le_trans (b:=r * (2*(θ r*(↑(M r):ℝ)^2))) (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (hx hij) hr.le).trans he)
        unfold role; push_cast; field_simp -- optional ring
   exact_mod_cast (le_of_mul_le_mul_left (le_of_mul_le_mul_left hh zero_lt_two) (C.S.a_pos _))

omit W fx
abbrev baseRail (C:Family G) (x:Points n)(r:ℝ):= address (role C r) x
def nextRail (C:Family G)(x:Points n) (i:Fin n)(j:Axis)(r:ℝ):= Difference.advance (baseRail C x r) i j 1
lemma leapsOnce {i:Fin n}{j:Axis}(hr:0<r) : tag (θ r) (nextRail C x i j r) = tag (θ r) (baseRail C x r)+ θ r• Points.direction i j:=by
   apply MulAction.injective₀ hr.ne'
   dsimp only
   rw [scaledRole hr,smul_add,scaledRole hr,smul_smul,show r * θ r=_ from (by unfold role; field_simp : r * θ r = a (K r))]
   exact turned_tags ..
include W fx
lemma reachesBase (x:Points n): Tendsto (fun r=> tag (θ r) (baseRail C x r)) home (𝓝 x):=by
   rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (positiveLength.mono (fun i hi=> approximate (div_pos (C.S.a_pos _) hi) _)) (by simpa only [mul_zero] using (stretches W fx).const_mul (4*n:ℝ))
lemma reachesNext (x:Points n)(i:Fin n)(j:Axis): Tendsto (fun r=> tag (θ r) (nextRail C x i j r)) home (𝓝 x):=by
   have hx:= (reachesBase W fx x).add ((stretches W fx).smul_const (Points.direction i j)); rw [zero_smul,add_zero] at hx; exact hx.congr' (positiveLength.mono fun _ hp=>(leapsOnce hp).symm)
end space
end YM.RG17
