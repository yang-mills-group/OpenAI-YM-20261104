import YM.OPE.Coverage.Signage
import YM.OPE.Coverage.Theory

/-! ## Physical nonzero flux survives centering on this OPE hierarchy -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.OPE.Coverage
open Function Set Filter Extraction Climb Ward Table Org Maxwell Spec Next.UVStress Extra Pert
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{C:Family G}{S:Table C.book}{F:Order}{V:DiffPlan S}{T:Lighthouse C.book}
set_option quotPrecheck false
local notation "s₀" => Bel C.book
variable (U:Final C F S)
local notation "E₀"=>U.sector.energy
local notation "E"=> reCenter S E₀
local notation "T₁"=>U.room.kernel
local notation "P"=>U.sector.derivatives
local notation "𝐚"=> U.sector.turns.lie
lemma centered_pre: Climb.Pre T₁ P E ((P).deriv) 𝐚:=by
   rcases U.phase.transport with ⟨iD,hV,hW,hR,hμ,-,hc,ht,ha⟩
   have hT:= UVNext.FreeStress.stays_tensor T₁ hR hμ ht
   have hB : RawTensor (T₁).spin E₀ := fun k a b=> (hR.signed 4 k _).symm.trans (ht (Signed.ortho k) a b)
   let v:KernelSpace (T₁).spin:=⟨E, enters T₁ _ (sym_mem.mpr ⟨hc.symmetric,hc.real,hB⟩) ⟩
   obtain ⟨e1,e2,e3⟩:=sym_mem.mp (kernel_mem.mp v.prop).1
   refine ⟨⟨e1,e2,fun j=>?_⟩,e3,?_⟩
   · change ∑ a, (P).deriv 4 a (centering S 4 _) = 0
     have hd := (P).unit_drop ((T₁).laws) hV ((T₁).smooth) 4
     simp_rw [value_center,map_sub,map_smul,hd,smul_zero,sub_zero,hc.divergence j]
   let down(i j):=-expectation S 4 ((E₀) i j)
   have he : v.val=E₀+UVNext.FreeStress.fossil down:=by
      funext i j
      change centering S 4 _ = (E₀) i j + down i j • _
      rw [value_center]; simp [down,sub_eq_add_neg]
   rw [show ((reCenter S) U.sector.energy) = _ + _ from he]; exact UVNext.FreeStress.add_unit T₁ ha down (fun i j => by dsimp [down]; rw [hc.symmetric i j])
lemma expectation_zero : WeakScaling.Centered E:=by
   intro i j
   rw [Work.A15.front_apply]
   refine Eq.trans ?_ (centers_field (T₁).laws ((E₀) i j)); rw [expectation,Work.A01.front_eval]
   apply congrArg _; exact congrArg (Fin.cons _) (Subsingleton.elim ..)

lemma physicalBorn (hG : G.Simple){X:Scaling S}(h:FirstExtension U X): (E: S.Stress) ≠ 0:= by
   obtain ⟨M,hM,-⟩:=Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
   refine WeakScaling.flux_nontrivial T₁ _ (centered_pre U).raw ?_
   intro hv
   apply M.lit.born
   have hx : leaves (S:=S) ((P).deriv) 4 = 0 :=congr_arg (fun q : Parts S=> leaves q 4) hv
   have hT:M.T.W= Maxwell.Free.scheme C.labels:=congr_arg Lighthouse.W hM
   rw [hT]
   have ht := h.derivatives 4
   unfold Bid.ConLap at ht
   simp only [hx,map_zero] at ht
   apply tendsto_nhds_unique ht
   exact tendsto_const_nhds.congr fun k => Eq.symm (funext fun j=> ContinuousLinearMap.ext (fun u=> show X.r k • ((0:(s₀).Field 4 →L[ℂ] (s₀).Field (4+1)) u) = _ from smul_zero _))
end YM.OPE.Coverage
