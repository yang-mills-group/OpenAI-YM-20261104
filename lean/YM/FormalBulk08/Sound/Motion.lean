import YM.FormalBulk08.Sound.Germ
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J:Type}{A:Levels G}{K:KernelChoices}{d j t:ℕ}{W:Lab G K I}{ρ:ChartRatio G}
variable (x:Leaf W.scrolls)(n:Side)
-- Books independent of η E and normalized marks through.
abbrev boxS := primary (W.pat x) K n
abbrev rug := Lodge.forest (S:=boxS x n) (W.wood x.a x.b)
abbrev PinL :=Pine G (boxS x n) (rug x n)

def densityP : Matrix (PinL x n) (PinL x n) ℝ:= ((North.Cov W x.a x.b).acts n).submatrix ((W.wood x.a x.b).splitting (S:=boxS x n)) ((W.wood x.a x.b).splitting (S:=boxS x n))
def costU := (dropRoot G (boxS x n) (rug x n))ᵀ

def scaleP :=
   let Q:=costU x n; let H:=patron G (Precision.probe (boxS x n))*Q
   let S:=sun (W.V x.a) K.penalty (x.b+1) (n*(W.pat x).L)
   Qᵀ*S*Q + K.penalty •(Hᵀ*H)
def conditionalV := Matrix.submatrix ((Mean W x.a x.b).acts n) ((W.wood x.a x.b).splitting (G:=G) (S:=boxS x n)) (id (α:=wire G n))
def ferryP (i:ℕ): Hull (PinL x n) (wire G n):= ferry (destination (W.V x.a) (seqN x i) x.b) (W.toEmpire.bill x.a x.b) (W.wood x.a x.b) n
lemma shipment {V I:Type*}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{H:ℕ→Matrix I V ℝ}{T:Matrix I V ℝ}(hp:Ends H T): Ends (fun i=>(H i)ᵀ) Tᵀ:= by apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp _) _
lemma knight {V:Type*}[Fintype V][DecidableEq V] {H₁ H₂:ℕ→Matrix V V ℝ}{T P:Matrix V V ℝ}(hp:Ends H₁ T)(h:Ends H₂ P) (he:∀ i,(H₁ i).PosDef)(hu:∀ i,H₁ i*H₂ i=1): T.PosDef ∧ T*P=1:= by
   have hv : T*P=1:= tendsto_nhds_unique (matrixPaid hp h) (tendsto_const_nhds.congr' (.of_forall fun i=>(hu i).symm))
   have hh i: (H₁ i)ᵀ=H₁ i:= (he i).isHermitian; have hT:Tᵀ=T:= tendsto_nhds_unique (shipment hp) (hp.congr' (.of_forall fun i=>(hh i).symm))
   have hP:T.PosSemidef:= by
      apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      refine ⟨hT,fun v=>?_⟩
      have hh : Ends (fun i=> star v ⬝ᵥ (H₁ i *ᵥ v)) (star v ⬝ᵥ (T *ᵥ v)):= by
          unfold dotProduct Matrix.mulVec; exact tendsto_finsetSum _ fun j _=>(tendsto_finsetSum _ (fun k _=>(tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp j) k).mul_const (v k))).const_mul (star v j)
      exact ge_of_tendsto' hh (fun i=>(he i).posSemidef.dotProduct_mulVec_nonneg v)
   exact ⟨(hP.posDef_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hv)),hv⟩
lemma adjusts (P:Flight j t)(L:Lodge P.patch)(K:KernelChoices)(n:Side)(ht:4≤ t): (pMean G K P n (Reef.floor K P L n))= Matrix.submatrix ((locating G K P L).acts n) (L.splitting (S:=primary P.patch K n)) id:= by
   obtain ⟨s,C,hs,hC,T⟩:= Bank.aone P G ht (K:=K); obtain ⟨U,h,H⟩:= Lodge.bothPay G K L _ hs
   have hv : (locating G K P L).acts n=repackM (L.splitting (S:=primary P.patch K n)) (Equiv.refl _) (pMean G K P n (Reef.floor K P L n)):= ((H _ C hC T).2.2 n).1
   rw [hv]; ext i j; unfold repackM ; simp
variable (hp:Use W ρ d)
lemma poles : Ends (fun i=>(ferryP x n i).saddle.P) (scaleP x n):= by
   let P i:= kernelP G K.penalty ((destination (W.V x.a) (seqN x i) x.b).wing) (n*(W.pat x).L); let A:= W.V x.a; let M:=n*(W.pat x).L; let V:=costU x n;let T:=patron G (Precision.probe (boxS x n))*V
   have ht: Ends P (sun (W.V x.a) K.penalty (x.b+1) M):= (tendsto_add_atTop_iff_nat _).mpr (cosmic _ _ K.penalty_pos (x.b+1) M)
   have h:Ends (fun i=> Vᵀ * P i * V) (Vᵀ * sun (W.V x.a) K.penalty (x.b+1) M * V):= matrixPaid (matrixPaid tendsto_const_nhds ht) tendsto_const_nhds
   exact h.add_const (K.penalty • (Tᵀ*T))
include hp
lemma gravity : Ends (fun i=>(ferryP x n i).saddle.q) (densityP x n):= by
   have he:= capital (hp.zero x) (ongoing hp x).2 n; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j;exact (tendsto_add_atTop_iff_nat _).mpr (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he _) _)
lemma strengthP: (scaleP x n).PosDef ∧ scaleP x n * densityP x n =1 := knight (poles x n) (gravity x n hp) (fun i=> (honey (destination (W.V x.a) (seqN x i) x.b) (W.toEmpire.bill x.a x.b) (W.wood x.a x.b) n).1) (fun i=> (ferryP x n i).saddle.inv)
lemma tree_resp : Ends (fun i=> pMean G K (destination (W.V x.a) (seqN x i) x.b) n (rug x n)) (conditionalV x n):= by
   have he:=capital (hp.zero x) (ongoing hp x).1 n; let p i:=destination (W.V x.a) (seqN x i) x.b
   have hx i:pMean G K (p i) n (rug x n)= Matrix.submatrix ((MeanP W x.a x.b (seqN x i)).acts n) ((W.wood x.a x.b).splitting (S:=boxS x n)) id:= adjusts (p i) (W.wood x.a x.b) _ _ ((W.V x.a).clock.adm x.b)
   apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
   change Tendsto (fun k=> pMean G K (p k) _ _ _ _) _ _; simp_rw [hx]; exact (tendsto_add_atTop_iff_nat _).mpr (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he _) _)
end YM.FormalBulk08.Sound
