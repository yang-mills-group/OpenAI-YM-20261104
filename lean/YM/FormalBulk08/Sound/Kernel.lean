import YM.FormalBulk08.Sound.Motion
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J:Type}{A:Levels G}{K:KernelChoices}{d j t:ℕ}{W:Lab G K I}{ρ:ChartRatio G}
variable (x:Leaf W.scrolls)(n:Side)
abbrev wingV (i:ℕ) : Matrix (PinL x n) (wire G n) ℝ := pMean G K (destination (W.V x.a) (seqN x i) x.b) n (rug x n)
variable (hp:Use W ρ d)
include hp
lemma bank_interest :
    let U:=costU x n; let V:= conditionalV x n; let Y:= U*V
    let Q:=patron G (Precision.probe (boxS x n));let S:=W.V x.a
    let Z:=sun S K.penalty (x.b+1) (n*(W.pat x).L); let z:=sun S K.penalty x.b n
    scaleP x n * V = K.penalty • (Q*U)ᵀ ∧ Yᵀ*Z*Y + K.penalty • ((1-Q*Y)ᵀ*(1-Q*Y))=z := by
    intro U V Y Q S Z z; let P i:= destination (W.V x.a) (seqN x i) x.b; let X i:= U*wingV x n i; let T i:=1-Q*(X i)
    have hs:=tree_resp x n hp; have h(i:ℕ):= normal G (P i) n (rug x n) ((W.V x.a).clock.adm _)
    refine ⟨tendsto_nhds_unique (matrixPaid (poles x n) hs) (tendsto_const_nhds.congr' (.of_forall fun i=> (h i).1.symm)), ?_⟩
    have hx: Ends X Y:= matrixPaid tendsto_const_nhds hs;have ht: Ends T (1-Q*Y):= tendsto_const_nhds.sub (matrixPaid tendsto_const_nhds hx)
    have he:Ends (fun i=> kernelP G K.penalty (P i).wing (n*(W.pat x).L)) Z:= (tendsto_add_atTop_iff_nat (x.b+1)).mpr (cosmic _ _ K.penalty_pos _ _)
    have hv:Ends (fun i=> kernelP G K.penalty (P i).land n) z:=by
         have hh i: (P i).land=location (W.V x.a) (seqN x i) x.b:= by rw [loc_land (W.V x.a) _ _ (show x.b<seqN x i by unfold seqN;omega)]
         simp_rw [hh]; exact (tendsto_add_atTop_iff_nat (x.b+1)).mpr (cosmic _ _ K.penalty_pos _ _)
    refine tendsto_nhds_unique ((matrixPaid (matrixPaid (shipment hx) he) hx).add ((matrixPaid (shipment ht) ht).const_smul K.penalty)) (hv.congr' (.of_forall fun i=> (h i).2.symm))

def hospital : Hull (PinL x n) (wire G n) :=
    let V:=conditionalV x n
    let Z:=densityP x n;let P:=scaleP x n
    { saddle:= { q:=Z,P:=P, ok:=fun i j=> tendsto_nhds_unique (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (gravity x n hp) _) _) ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (gravity x n hp) _) _).congr' (.of_forall fun k=> ((ferryP x n k).saddle.ok i j).symm)),valid :=fun i j=> ((strengthP x n hp).1.isHermitian.apply j i), inv:=(strengthP x n hp).2 }
      drift:= draught V
      main:=crunch (sun (W.V x.a) K.penalty x.b n) }
variable (a:hue G)(h:LocalRatio ρ)(hs:G.Simple)
include h hs
lemma heir_zero (m:Side):coeff 0 (stone (heir a ρ W x.a x.b) m)=crunch (sun (W.V x.a) K.penalty x.b m):= by
    let V:= stopper (heir a ρ W x.a x.b) d; rw [←stopper_presents (Nat.zero_le d)]; obtain ⟨C,s,hC,hv,T⟩:=rose_live (W.V x.a) K.penalty K.penalty_pos x.b; exact stoned_main hv.le hC.le T.value (born a x hp h hs) (show V 0 2=setkin G (rose _ _ _) from congr_fun (if_pos (Nat.zero_le d) : V 0=_ ) 2|>.trans (virgin_ink a x hp h hs)) _
lemma bedded (k:(boxS x n).Choices):
     let F:= rug x n
     Solved (hospital x n hp) (flush F k ρ (stone (heir a ρ W x.a (x.b+1)) (n*(W.pat x).L))) := by
    intro F; let L:= n*(W.pat x).L;let U:=costU x n; let V:=conditionalV x n;let Z:=sun (W.V x.a) K.penalty (x.b+1) L;let z:=sun (W.V x.a) K.penalty x.b n;let T:=hospital x n hp
    have hS:= W.toEmpire.bill x.a x.b; have hx:coeff 0 (stone (heir a ρ W x.a (x.b+1)) (n*(W.pat x).L))=crunch Z:=heir_zero (North.porch x) hp a h hs _
    apply duet; intro i j
    rw [toInk_value i j T,flush,map_add,Reef.halo_zero F ρ h,add_zero,attested,in_value (show (boxS x n).patch.Branches _ _ from hS),hx,map_add, levelDp,duplex_C]
    let y:=i+ V *ᵥ j
    have he : graft F (Sum.elim (fun i' => i i'+traceP j (T.drift i')) j) = Sum.elim (U *ᵥ y) j:= by rw [show (fun i' => i i'+traceP j (T.drift i'))=y from congr_arg (i+·) (draught_fee V j)]; rfl
    rw [he,crunch_value, show T.main=crunch z from rfl, crunch_value, trace_base] -- tune
    let A:= Uᵀ*Z*U; let e:= patron G (Precision.probe (boxS x n)); let Y:= e*U
    obtain ⟨hp',hu⟩:=bank_interest x n hp; let P:= scaleP x n; have hP: Pᵀ=P:=(strengthP x n hp).1.isHermitian
    have hb: Vᵀ*A*V+ K.penalty • ((1-Y*V)ᵀ*(1-Y*V))=z:= by rw [←(show (U*V)ᵀ*Z*(U*V)+ K.penalty • ((1-e*(U*V))ᵀ*(1-e*(U*V)))=z from hu)]; simp only [A,Y,Matrix.mul_assoc,Matrix.transpose_mul]
    have hh:= additive_balance K.penalty P A Y V z i j rfl hP hp' hb
    have hg:y ⬝ᵥ (A*ᵥ y)=(U*ᵥ y) ⬝ᵥ (Z*ᵥ (U*ᵥ y)) := by unfold A; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    change dotProduct y (A*ᵥ y)+ K.penalty*dotProduct (j-Y*ᵥ y) (j-Y*ᵥ y) = _ at hh
    rw [hg,show Y*ᵥ y=e*ᵥ (U*ᵥ y) from (Matrix.mulVec_mulVec y e U).symm] at hh; change -dotProduct (U*ᵥ y) (Z*ᵥ (U*ᵥ y))/2 - K.penalty*dotProduct (j-e*ᵥ (U*ᵥ y)) (j-e*ᵥ (U*ᵥ y))/2= -dotProduct i (P*ᵥ i)/2 + _; linarith only [hh]
end YM.FormalBulk08.Sound
