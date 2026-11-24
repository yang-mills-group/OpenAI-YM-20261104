import YM.FVA2.Lambda.Quad
/-!
# d=4 rung B₁ (and lifted-rank vertices). Antifield comparison
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Slice
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:ℕ}
lemma r_Lie (i j k:G.ColorIndex): rune i j k=Mark.LieColor i j k:= by unfold rune; rw [scaled_tensor]
lemma r_sq (i:G.ColorIndex)(h:G.Simple): ∑ j:G.ColorIndex,∑ k:G.ColorIndex,(rune i j k)^ (2:ℕ)=(G.casimir:ℂ):= by
    let b: OrthonormalBasis G.ColorIndex ℝ G.Color:= EuclideanSpace.basisFun G.ColorIndex ℝ
    have he:= Gauge.trace_adjoint h ( b i ) ( b i ); change G.minusKilling (b i) (b i)=_ at he; rw [b.inner_eq_one, mul_one,Gauge.minusKilling_sq _ b ] at he; unfold rune; rw [← he]; push_cast; refine Finset.sum_congr rfl fun j _=> ?_; norm_cast; simp_rw [ Native.scaled_tensor ]; -- inner swap prove
    exact b.sum_sq_inner_left (G.ad (b i) (b j))
lemma jawrank (F H:Mield G n)(hx:∀ i, Book.rank 1 (F i))(hp:∀ i, Book.rank 1 (H i))(i:G.ColorIndex): Book.rank 2 (jaw G n F H i):= by rw [chew]; exact Rails.sum _ (fun j _=> Rails.sum _ (fun v _=> Rails.smul _ ( (hx j).product (hp v) )))
lemma quillRank (i j:Arts.L n)(k:G.ColorIndex): Book.rank 2 (quill i j k):= jawrank _ _ (fun _=> mon_leaf _ ) (fun _=> mon_leaf _ ) k
lemma blazeRank (z:Chan G n): Book.rank 2 (blazeV G n z):= by rcases z with ⟨_|z,i⟩; exact Rails.smul _ (jawrank _ _ (fun _=> mon_leaf _) (fun _=> mon_leaf _) i); exact jawrank _ _ (fun _=> mon_leaf _) (fun _=> mon_leaf _) i
lemma B₁_rank (G:Gauge)(n:ℕ): Book.rank 3 ( B₁ G n ):= by
    refine Rails.add ?_ ?_; refine Rails.smul _ (Rails.sum _ (fun i _=> Rails.sum _ (fun j _=>?_ )))
    · exact Rails.add ( Rails.sum _ (fun k _=> ( rank_α i j k ).product ( quillRank i j k )) ) ( Rails.sum _ (fun k _=> (quillRank i j k).product ( rank_α i j k )) )
    exact Rails.sum _ (fun i _=> Rails.smul _ (( mon_leaf _ ).product ( blazeRank i )) )
lemma force (a:Chan G n)(p:SectorP n)(w:List (Shore G n)): B₁ G n ((onX true a,p)::w)= Motif.phase a * blazeV G n a w := by
    let v:= (onX true a,p)::w; have hv: B₂ G n v=0:= congr_fun (noteX p a) w; obtain he:= congr_fun (congr_fun (Class_at G 1) n) v; simp only [χ,map_add, Literal.value_sl,one_pow,one_smul, Pi.add_apply, Pi.sub_apply, hv,add_zero] at he; unfold v at he; rw [he, Captain, Captain, zonal a 1,one_smul,Pi.add_apply]; ring
lemma ghostQ (i j:Arts.L n)(z y u:G.ColorIndex)(p q r:SectorP n): B₁ G n [ (onX true (some i,z),p), (onX false (some j,y),q), (onX false (none,u),r) ]= if i=j then rune y u z else 0:= by
    rw [ force ]; unfold blazeV; simp only [chew,Finset.sum_apply, Pi.smul_apply,Motif.phase ]; simp_rw [ Motif.pairv (F:=A n G i _) (H:=cwave n G _) ( mon_leaf _ ) ( mon_leaf _ ) ]; by_cases h:i=j <;> simp [h,Motif.A,cwave,lip,Motif.leaf,onX,node1,cross,eq_comm (a:=j) (b:=i),mul_ite]
lemma spirit (i j k:G.ColorIndex)(p q r:SectorP n): B₁ G n [ (onX true (none,i),p),(onX false (none,j),q),(onX false (none,k),r) ]=rune j k i:= by
    rw [ force ]; unfold blazeV; unfold Sc; simp only [ Pi.smul_apply,smul_eq_mul,Motif.phase,chew,Finset.sum_apply ]; simp_rw [pairv (F:=cwave n G _) (H:=cwave n G _) ( mon_leaf _ ) ( mon_leaf _ ) ]; -- sums
    simp [ cwave,onX, Landau.parity,Landau.p, lip, Motif.leaf, node1, field,cross, mul_ite, mul_add, Finset.sum_add_distrib]; rw [r_ortho j k]; ring
open Canvas (triple)
local notation "Ψ"=>field ( parity (C:=G.ColorIndex) (A:=Axis) )
lemma trank (w:List (Lane4 G))(he:w.length≠3): triple G w=0:= by unfold triple; rw [pulse1]; apply B₁_rank G 0; rw [Book.mod_int]; omega
lemma tghost (w:List (Lane4 G))(he:fieldDim ghostNo w≠0): triple G w=0:= ( fund_one G 0 ).ghost w he
lemma tflip₁ (x y z:Lane4 G) : triple G [x,y,z]=cross (Ψ x) (Ψ y) *triple G [y,x,z]:= (fund_one G 0).sym [] x y [z]
lemma tflip₂ (x y z:Lane4 G) : triple G [x,y,z]=cross (Ψ y) (Ψ z)*triple G [x,z,y]:= (fund_one G 0).sym [x] y z []
variable (a b:Axis)(i j k:G.ColorIndex)(p q r:QP)
abbrev delta (a b:Axis):ℝ:= if a=b then 1 else 0
lemma t_UWC : triple G [U a i p,W b j q,C k r]=rune j k i* (Slice.delta a b:ℂ):= by unfold triple; rw [pulse1]; obtain h:= ghostQ (n:=0) a b i j k p q r; exact h.trans (by split <;> next he=> simp )
lemma t_UCW : triple G [U a i p,C k r,W b j q]=rune j k i * (Slice.delta a b:ℂ):= by rw [ tflip₂, t_UWC ]; exact one_mul _
lemma t_CUW : triple G [ C k r,U a i p,W b j q]= -(rune j k i) * (Slice.delta a b:ℂ):= by rw [ tflip₁, t_UCW ]; change -(1:ℂ)*_=_; ring
lemma t_WUC : triple G [W b j q,U a i p,C k r]=rune j k i* (Slice.delta a b:ℂ):= by rw [ tflip₁, t_UWC ]; exact one_mul _
lemma t_CWU : triple G [ C k r,W b j q,U a i p]= -(rune j k i) * (Slice.delta a b:ℂ):= by rw [ tflip₂, t_CUW ]; exact one_mul _
lemma t_WCU : triple G [W b j q,C k r,U a i p]= -(rune j k i) * (Slice.delta a b:ℂ):= by rw [ tflip₁, t_CWU ]; exact one_mul _
lemma t_SCC : triple G [ Detect.S i p,C j q,C k r ]=rune j k i:= by unfold triple; rw [pulse1]; exact spirit (n:=0) i j k p q r
lemma t_CSC : triple G [C j q,Detect.S i p,C k r]= rune j k i:= by rw [ tflip₁,t_SCC ]; exact one_mul _
lemma t_CCS : triple G [C j q,C k r,Detect.S i p]= rune j k i:= by rw [ tflip₂,t_CSC ]; exact one_mul _
end YM.FVA2.Lambda.Slice
