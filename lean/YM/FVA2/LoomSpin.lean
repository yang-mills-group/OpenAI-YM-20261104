import YM.FVA2.PhysicalDeck
import YM.X.Dial.Round
/-!
# The *whole*, engineering-renormalized with Wick top W Native amplitude
 is signed-turn compatible in exactly the needed stencils. No matrix rotation
 performed before W's action on all the tied slots.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2
open Filter Topology Set Function MeasureTheory PertExtension
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Paint
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.Book.Convolve MS.Plane MS.Tone MS.Color
open Local.Physical MS.Menus Plate Labels Source
open scoped Topology Classical ContDiff
variable {G:Gauge}
namespace Warehouse
variable (TQ: Warehouse G)(d:ℕ)
local notation "Ξ"=> TQ.scene d
local notation "ΠP"=> TQ.scopeW d
local notation "Γ"=> TQ.F
local notation "H"=> inftyQ G
variable (k:Signed)
section poses
open YM.Source
lemma actcoord_real (j i:(TQ.scene d).Index) :
   (↑(((TQ.scene d).act k.ortho (Pi.single j 1)) i).re:ℂ)= ( (TQ.scene d).act k.ortho (Pi.single j 1) i):= by
     let F:= (TQ.scene d); apply Complex.conj_eq_iff_re.mp; change star _=_; rw [ ← F.conj_basis (F.act k.ortho ( Pi.single j 1 )) i, ← F.coords_basis j,F.act_coords,F.coords.symm_apply_apply, real_turn,F.realForm]

private lemma copied {i:TQ.Atom d}(n:Side): shown n (TQ.artifact d i)= region.symm (reads (put (bare (TQ.S d) i) (0:Site n) ∘ nation)):= by
     obtain hp:= (TQ.poised d i).pays n 0; rw [shift_nil] at hp; exact Subtype.ext hp.home
private lemma freeBasis (x:(TQ.scene d).Coeff): x= ∑ i:TQ.Atom d,x i • Pi.single i (1:ℂ):= by
   ext i; rw [Finset.sum_apply]; simp [ Pi.single_apply, apply_ite]

lemma posed_seed (i:TQ.Atom d): Native.Orient.pose k (TQ.artifact d i)=∑ j:TQ.Atom d,(((TQ.scene d).act k.ortho (Pi.single i 1)) j) • TQ.artifact d j := by
   let Z:= (TQ.S d); let B (j:TQ.Atom d):= bare Z j; let x := (TQ.scene d).act k.ortho (Pi.single i 1); refine (markEq ..).mp (Eventually.of_forall ?_); intro n
   let f (j:TQ.Atom d): City G (Site n)→ℝ:= put ( B j ) (0:Site n) ∘ nation; let g:= Native.Orient.affine (G:=G) (R:=Per n) k
   have hv : f i ∘ g= ∑ j:TQ.Atom d, (x j).re • f j:= by
       funext w; unfold f B g; rw [comp_apply,comp_apply, Native.Orient.at_nation, Plate.bare_put ];
       unfold PertExtension.Orb.SlotEvaluation.fieldAt YM.Source.SectionData.places; rw [expandAt_pull ( 0:Site n ), show Lattice.affine k 0 (0:Site n)=0 from (by simp [Lattice.affine]), (TQ.h d).Hpart ]; rw [Finset.sum_apply];
       let O:((TQ.scene d).Coeff)→ₗ[ℂ] ℂ:= { toFun t:= (Z.evaluate t (expandAt (0:Site n) (nation w))), map_add' p q:= by unfold YM.Source.SectionData.evaluate; simp, map_smul' p q:= by unfold YM.Source.SectionData.evaluate; simp }; change (O x).re=_; nth_rw 1 [freeBasis TQ d x]; rw [map_sum, Complex.re_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; nth_rw 1 [← (show (↑((x j).re):ℂ)= x j from TQ.actcoord_real d k i j)]; rw [smul_eq_mul,Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; rfl
   have hh(j:TQ.Atom d): germ (f j):=pos_jet (TQ.poised d j) _
   rw [ travel_t, map_sum, copied ]; apply Subtype.ext; rw [pose_rule k (hh i),hv,sum_stack]; simp_rw [map_smul]; rw [reads,Taylor.ink_sum (F:=fun j=>(x j).re • f j) _ _ (fun j _=> (hh j).const_smul (x j).re)]; apply Finset.sum_congr rfl; intro j _; rw [Taylor.ink_smul _ (hh j),copied, Submodule.coe_smul, show (↑((x j).re):ℂ)=_ from TQ.actcoord_real d k i j ]; rfl

private lemma turn_q (b₀: Labels.Label G d) (m₀:ℕ×ℕ)(hf:b₀∈Labels.Grade m₀): Labels.tensor k.ortho b₀∈ Labels.Grade m₀:= by obtain he:=gradePart_mem m₀ (Labels.tensor k.ortho b₀); rwa [gradePart_turn, gradePart_self _ _ hf] at he
private lemma off_grade (i j:TQ.Atom d)(h:(TQ.scene d).grades i≠(TQ.scene d).grades j): (TQ.scene d).act k.ortho (Pi.single i 1) j=0:= by rw [← (TQ.scene d).coords_basis i,(TQ.scene d).act_coords]; exact (TQ.scene d).power_coefficient j h (turn_q d k _ _ ((TQ.scene d).pure i))

abbrev marked (d:ℕ) : (TQ.scene d).Coeff →ₗ[ℂ] T (Glow G) := ∑ i:TQ.Atom d, LinearMap.smulRight (LinearMap.proj i) (TQ.inkB d i)
lemma mark_at (v:(TQ.scene d).Coeff): TQ.marked d v=∑ j:TQ.Atom d,v j • TQ.inkB d j:= by rw [marked,LinearMap.sum_apply]; rfl
lemma mark_own (i:TQ.Atom d) : TQ.marked d (Pi.single i 1) = TQ.inkB d i := by rw [mark_at,Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun j hj hi=> by rw [Pi.single_eq_of_ne hi,zero_smul])]; simp
abbrev markPose (k:Signed) := promote (pose (R:=ℤ) (G:=G) k)
lemma posed_inkB (i:TQ.Atom d) : markPose k (TQ.inkB d i)=TQ.marked d ((TQ.scene d).act k.ortho (Pi.single i 1)):= by
   rw [mark_at]; unfold inkB; funext n; rw [ markPose, promised,levels,poseModel, TQ.posed_seed d k i,map_sum, Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_ ; by_cases hx:(TQ.scene d).grades i=(TQ.scene d).grades j; · simp_rw [map_smul, grade, hx ]; rfl
   rw [ TQ.off_grade d k i j hx,zero_smul,map_zero,zero_smul ]; rfl
lemma marks_comm (v:(TQ.scene d).Coeff): TQ.marked d ((TQ.scene d).act k.ortho v)= markPose k (TQ.marked d v):= by
    rw [ freeBasis TQ d v, map_sum,map_sum,map_sum,map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [map_smul,TQ.mark_own, TQ.posed_inkB]

abbrev insertW (d:ℕ) := TQ.marked d ∘ₗ (TQ.scopeW d).inverse (inftyQ G) ∘ₗ (TQ.scene d).coords.toLinearMap
lemma whirl (q: Label G d): TQ.insertW d ( Labels.tensor k.ortho q )= markPose k (TQ.insertW d q):= by
   let F:= TQ.scene d; change TQ.marked d ((TQ.scopeW d).inverse (inftyQ G) ( F.coords _ ))= _; rw [ ← F.act_coords,← PositionX.Dial.r_spin (TQ.S d) k (TQ.h d) (TQ.acts d), marks_comm ]; rfl
lemma describes (B: Local.Physical.Deck G)(r:ℕ)(i:B.BIndex d r) : ( TQ.native B ).inkM d r i= TQ.insertW d (Warehouse.label B d r i) := by unfold native insertW; simp_rw [code,TQ.price_cast, LinearMap.comp_apply,TQ.mark_at]; rfl
lemma pose_train (p:Team)(x:ℝ)(i:ℕ)(f:Glow G) : Native.Orient.pose k (train (fieldV p x∘Prod.fst) i f)=train (fieldV p x∘Prod.fst) i (pose k f):= by
   have hb (j: LightMode G Cover): fieldV p x (Orient.turn k j).1= fieldV p x j.1:= by rcases j with ⟨⟨⟨_|j,t⟩,u⟩,x⟩ <;> rfl
   have hc : graffiti (Orient.σ k) (train (fieldV p x∘Prod.fst) i f)=train (fieldV p x∘Prod.fst) i (graffiti (Orient.σ k) f):= Subtype.ext (funext fun _=>mul_left_comm ..)
   unfold pose; rw [LinearMap.comp_apply,hc]; exact pennant_ferry (turn k) (PowerSeries.coeff i) (fieldV p x∘Prod.fst) (fieldV p x∘Prod.fst) (fun t=> (hb t).symm) _
lemma wobble_pose (p:Team)(x:ℝ)(V:T (Glow G)) : markPose k (wobble G p x V)= wobble G p x (markPose k V):= by
   rw [markPose,wobble, LinearMap.comp_apply, LinearMap.comp_apply, ← Program.comm (shift p x) V ]; funext n; simp only [promised, rolls,map_sum,pose_train ]
end poses
end Warehouse
end YM.FVA2
