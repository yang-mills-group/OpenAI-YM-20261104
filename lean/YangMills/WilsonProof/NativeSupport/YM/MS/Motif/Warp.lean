import YM.MS.Motif.Warp
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Pulp
/-!
# The actual classical master checked on any formal z value

No Δ# master.Cape.Fields vary all at once. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{n:ℕ} {U V :Mield G n} {b:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 " ⋄ "=> product S
variable (z:ℂ)
local notation "g"=> cwave n G
local notation "Ω" => jaw G n
local notation "σ"=> dot (applyS z G n)
local notation "Sg"=> forge σ
local notation "Γ"=> A n G
-- commutator check all parities, differentiation ord.Label
lemma SQa (i:Arts.L n): Sg (convoke z i g)=0:= by
   let A:= convoke z i g; let K:= Ω A g; have H: Ω g A=K:= by simpa only [cross_true,neg_neg,one_smul] using (jaw_skew (G:=G) ghMd.tune ( heatSA z _ g ghMd i).tune);
   rw [S_D,S_C,Sc,map_smul,civil_d _ _ ghMd.tune,H]; change (-z/2:ℂ) • (K+K)+ z • K=0; rw [smul_add,← add_smul,← add_smul,show -z/2 + -z/2 + z=0 by ring,zero_smul]
lemma SQc : Sg (Sc z G n)=0:= by
   let W:= Ω g g; let T:= Ω g W; have hT: Ω W g= - T:= by simpa only [cross_false,neg_one_smul] using jaw_skew (b:=false) (jaw_p ghMd.tune ghMd.tune) ghMd.tune;
   obtain hh:=law (G:=G) (F:=g) (U:=g) (W:=g) ghMd.tune ghMd.tune; rw [ hT,cross_true,neg_one_smul ] at hh; change T = - T + - T at hh
   have hp:T=0:= by funext k l; obtain he:= congr_fun (congr_fun hh k) l; simp only [ Pi.add_apply,Pi.neg_apply] at he; change T k l=0; linear_combination he/3
   rw [Sc,map_smul, deriv_v z ghMd g, S_C]; change _ • (Ω (_ • W) g + cross true true • Ω g (_ • W))=_;
   rw [map_smul,map_smul,LinearMap.smul_apply,hT,show Ω g W= T from rfl,hp]; simp
lemma Sq (i:Chan G n): σ (applyS z G n i)=0:= by rcases i with ⟨_|i,c⟩; exact congr_fun (SQc z) c; exact congr_fun (SQa z i) c
lemma sume_high (hp:Mood false U): Pure S false (sume U U)∧ fieldSection false (sume U U)∧ σ (sume U U)=∑ i:G.ColorIndex, (2:ℂ) • ( (Sg U i) ⋄ U i ):= by
    unfold sume; refine ⟨ Pure.sum _ (fun i _=> (hp.tune i).prod (hp.tune i)), section_sum _ (fun i _=>section_p (hp.rank i) (hp.rank i)),?_⟩;
    rw [map_sum]; refine Finset.sum_congr rfl (fun i hi=>?_); unfold bite; rw [dot_pair (application z) (hp.tune i), (hp.tune i).central (σ (U i)),cross_false',one_smul, two_smul]; rfl
lemma sume_v (a b:Arts.L n)(h:Mood (G:=G) false (cur z a b)): σ (sume (cur z a b) (cur z a b))=0:= by
    rw [( sume_high z h).2.2]; simp_rw [ horr z a b, Pi.smul_apply,map_smul, LinearMap.smul_apply, ← Finset.smul_sum,ground h.tune, smul_zero]
lemma core_g : Pure S false (core G n z)∧ fieldSection false (core G n z)∧ σ (core G n z) = 0:= by
    unfold core; refine ⟨ Pure.smul _ ?_,?_,?_⟩; · exact Pure.sum _ fun a _=> Pure.sum _ fun b _=> (sume_high z ( curs z a b)).1
    · intro u v; rw [ map_smul, show D (onX (!false) u,v) (∑ a:Arts.L n,∑ b:Arts.L n,sume (cur z a b) (cur z a b))=0 from section_sum _ (fun a _=>section_sum _ (fun b _=>(sume_high z (curs z a b)).2.1)) u v, smul_zero] -- danger type
    simp_rw [map_smul,map_sum,sume_v z _ _ (curs z _ _)]; simp
lemma AllMaster {l:Legs (Shore G n)}(ht:net l=0): tree parity ( Wick.D0 G n) ( ploy G z n) (ploy G z n) l=0:= constitution (application z) (core_g z|>.1) (core_g z|>.2.1) (core_g z|>.2.2) (Sq z) ht
end YM.MS.Motif
