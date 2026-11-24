import YM.RG11Proof.Stress.Bullet
/-! # Mandates actually rank on the separated Stress coefficients at k

KernelSpace free pivots -- translate abstract questions on distributions to
the rank via `voice`, shapes all labels through 4. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.RG11.Stress
open YM.RG11.Fields YM.RG11.Jets YM.RG11.Nodes
open scoped Topology ContDiff Classical BigOperators
open Maxwell Labels Table Climb Work.A01 Next.UVStress UVNext.FreeStress Function Filter Set MeasureTheory Analysis Pert.Position
open PowerSeries
variable {G:Gauge}{F:Frames G}(A:ShapeReport G F)(B:Adapted F 4)

-- Evaluation multilinear on basis & all fields.
def test_columns {d n}(φ: spot n→ₗ[ℂ] ℂ)(k:ℕ):MultilinearMap ℂ (fun _:Fin n=>E F d) ℂ where
   toFun v:= φ (voice A v k)
   map_update_add' v j a b:=by
       rw [show voice A (update v j (a+b)) k=voice A (update v j a) k+voice A (update v j b) k from ?_,map_add]
       ext1 t; exact (A.table k d _ t).map_update_add ..
   map_update_smul' v j a b:=by
       rw [show voice A (update v j (a • b)) k=a • voice A (update v j b) k from ?_,map_smul]
       ext1 t; exact (A.table k d _ t).map_update_smul ..

@[simp] theorem hears_site {n}(φ:clean n→ₗ[ℂ] ℂ)(v:Fin n→E F 4):
   test_columns A (lift φ) 0 v=φ (dress (site F v) (site_smooth v)):=by
   change lift φ (voice A _ 0)=_; rw [origin4,lift_at]

/-- Set aside head field. -/
def leaves {n}(φ : clean (n+1)→ₗ[ℂ] ℂ)(a:E F 4):MultilinearMap ℂ (fun _:Fin n=>E F 4) ℂ:=
   (test_columns A (lift φ) 0).curryLeft a

theorem leaves_eq {n}(φ : clean (n+1)→ₗ[ℂ] ℂ)(a:E F 4)(v:Fin n→E F 4):leaves A φ a v=
   test_columns A (lift φ) 0 (Fin.cons (α:=fun _:Fin (n+1)=> E F 4) a v):=rfl

theorem extends_arm {n}(φ:clean (n+1)→ₗ[ℂ] ℂ)(D:B.toBasis.J→ℝ)(w:Fin n→B.toBasis.J):
     armed (R:=ℂ) (fun z=>(D z:ℂ)) (fun v=>constantCoeff (survey A B.toBasis φ v)) w=
       leaves A φ (B.toBasis.put D) (B.b ∘ w):=by
   rw [Basis.put_sum]
   unfold leaves; simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
   refine Finset.sum_congr rfl (fun i _=>congrArg ((D i:ℂ)* ·) ?_)
   dsimp only; rw [survey_zero4]; change _=test_columns (d:=4) (n:=n+1) A (lift φ) 0 (Fin.cons (α:=fun _:Fin (n+1)=>E F 4) (B.b i) (B.b ∘ w)); rw [hears_site]
   have he : B.b ∘ (Fin.cons (α:=fun _:Fin (n+1)=>B.toBasis.J) i w)=Fin.cons (B.b i) (B.b ∘ w):=comp_cons ..
   simp only [he]

-- from all spectator values on B.b -> all test passes vanish
 theorem kindles {n}(K:Axis→(clean (n+1)→ₗ[ℂ] ℂ))(X:Rect Taps B.toBasis.J ℝ)
    (he:∀ w, (∑ i:Taps,armed (R:=ℂ) (fun j=>(X i j:ℂ)) (fun v=>constantCoeff (queryHeads A B.toBasis K i v)) w)=0)(v:Fin n→E F 4):
     (∑ i:Axis,leaves A (K i) (disclose B X i 0) v)=0:=by
   let L(i:Taps):MultilinearMap ℂ (fun _:Fin n=> E F 4) ℂ := leaves A (shellers K i) (disclose B X i.1 i.2)
   have ht: (∑ i:Taps,L i)=0:=Module.Basis.ext_multilinear (fun _=>B.b) (fun w=>by
     rw [_root_.sum_apply]; simp_rw [queryHeads,extends_arm] at he; exact he w)
   have hz:=DFunLike.congr_fun ht v
   have hL(i j:Axis)(h:j≠0): L (i,j) v=0:=by unfold L; rw [shellers,if_neg h,leaves_eq,hears_site]; rfl
   change (∑ i:Axis × Axis,L i) v=0 at hz
   rw [Fintype.sum_prod_type] at hz
   simp only [_root_.sum_apply] at hz
   have he (i:Axis): (∑ j:Axis,L (i,j) v)=L (i,0) v:=Finset.sum_eq_single_of_mem (0:Axis) (Finset.mem_univ _) (fun j _ h=> hL i j h)
   exact Eq.trans (show (∑ i:Axis, leaves A (K i) (disclose B X i 0) v)=∑ i:Axis,∑ j:Axis,L (i,j) v from Finset.sum_congr rfl (fun i _=>by rw [he]; unfold L shellers; rw [if_pos rfl])) hz

 theorem ranking (hG:G.Simple){χ:E4→ℝ}(hw:Window (camera 0) χ)(X:Rect Taps B.toBasis.J ℝ)(hx:X∈candidate B)
    (he:∀ w,(∑ i:Taps,armed (R:=ℂ) (fun j=>(X i j:ℂ)) (fun v=>constantCoeff (queryHeads A B.toBasis direct i v)) w)=0)
    (ht:∀ w,(∑ i:Taps,armed (R:=ℂ) (fun j=>(X i j:ℂ)) (fun v=>constantCoeff (queryHeads A B.toBasis (traded hw) i v)) w)=0):X=0:=by
   apply disclose_inj B; rw [disclose_zero]
   apply congrArg Subtype.val (β:=((freeTable F).Stress)) (α:= KernelSpace (Free.spin_free F)) (a₁:= ⟨disclose B X,admitted B hx⟩) (a₂:=(0:KernelSpace (Free.spin_free F)))
   apply ignites _ hG hw
   · intro v; convert! kindles A B direct X he v using 1
     simp_rw [leaves_eq,hears_site,direct,on_at]
   intro v; convert! kindles A B (traded hw) X ht v using 1
   simp_rw [leaves_eq,hears_site,traded,run_at]
end YM.RG11.Stress
