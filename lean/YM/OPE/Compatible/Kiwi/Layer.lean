import YM.OPE.Compatible.Kiwi.Carry
/-! # Wick product estimates forest. Merge two ordered sets -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{U:Gloam}{P:ChartRatio G}{d k j r w e e' m:ℕ} {I J V:Type}{ℓ:Filter V}[LinearOrder I][LinearOrder J]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
variable (H:∀ i, Even (U.M i).val)
-- Vine char actual with zero closure. physical arcs supplementary
inductive Palm (e:ℕ): IpT H G→ Prop
| vine {p} : Vine H e p→Palm e p
| empty: Palm e 0
| add {a b}: Palm e a → Palm e b → Palm e (a+b)
| scale (r:ℝ){p}:Palm e p→ Palm e (r • p)
variable (A: Saga G e k)(p q: Nestle.Crew U)
abbrev Wish (A:Saga G e k)(H:Even N.val)(x:Site N):= Phi A firm (fun v=> poseT H x v.2 v.1)
def shade : IpT H G:= fun i=> Wish A (H i) (p.val i)
lemma zero_shade : shade H (Saga.empty (k:=k) (G:=G) (e:=e)) p=0:=rfl
lemma add_shade (B: Saga G e k) : shade H (Saga.add A B) p=shade H A p+shade H B p:=rfl
lemma mul_shade (r:ℝ):shade H (Saga.sml r A) p=r • shade H A p:=rfl
lemma plume (B:Saga G e' r)(hp:p≠q)(hq: SpareW p q)(hh:SpareW q p):Palm H (e+e') (shade H A p*shade H B q):=by
    induction A with
    | mon a ht hs=>
         induction B with
         | mon b hy k=> exact Palm.vine (sceneMon p q H a b ht hy hp hq hh)
         | empty=> rw [zero_shade,mul_zero]; exact Palm.empty
         | add b d ih hr=> rw [add_shade,mul_add]; exact Palm.add ih hr
         | sml a b ht=> rw [mul_shade,mul_smul_comm]; exact Palm.scale a ht
    | empty=>rw [zero_shade,zero_mul]; exact Palm.empty
    | add a b ih he=> rw [add_shade,add_mul]; exact Palm.add ih he
    | sml r a ih=> rw [mul_shade,smul_mul_assoc]; exact Palm.scale _ ih
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G} {Q:Seasons B}{Z:Alps B Q i l}
local notation "W"=> (fun p:ℕ=> Chart.tangent G (Weir.Limb (H p)))
local notation "Θ" h=> (fun p:ℕ=> boost (H p) (Train.top i) h B.K (G:=G))
lemma BondPalm {f:IpT H G}(h:Palm H e f)(i:ℕ): Bond (f i):=by induction h with
   | vine h=> exact vineCharge H h i
   | empty=> exact Bond.zero
   | add _ _ I Y=> exact I.add Y
   | scale a _ I=> exact I.scale a
lemma authorize (ht:4 ≤ i){f:IpT H G}(h:Palm H e f): GammaSite U e (fun j=>((Θ ht) j).average (W j) (f j)):=by induction h with
   | vine hv=> obtain ⟨a,hA⟩:=leadingPull (B:=B) (i:=i) (h:=ht) H hv; exact hA.2.1
   | empty=> convert! GammaSite.groom_zero U e using 2 with j; exact singleConst ..
   | @add a b h g I Y=> unfold GammaSite; convert! I.fuse Y using 2 with j; change _*( ((Θ ht) j).average (W j) _)= _+_; rw [Pi.add_apply,sun (W j) _ (BondPalm H h j) (BondPalm H g j),mul_add] -- cases syntax
   | scale a _ I=> unfold GammaSite; convert! I.glu (a • ContinuousLinearMap.id ℝ ℝ) using 2 with j; simp_rw [Pi.smul_apply,scooted]; simp;ring
lemma indemnify (ht:4≤ i){f:IpT H G}(h:Palm H e f)(hs:Z.gear=Train.top i)(hG:G.Simple)(hp:∀ i,Track Z (U.M i)): Fruit U e (fun j=>((Θ ht) j).average (W j) (f j*Shrew.Trill (anthem G (H j)))) 0:=by induction h with
   | vine h=>exact bodyP H h hs hG hp
   | empty=> simp only [Pi.zero_apply,zero_mul, show ∀ j, ((Θ ht) j).average (W j) 0= 0 from fun j=>singleConst ..]; exact (cleared_zero U).sap
   | @scale c f _ ht'=> have he:=Nestle.payScalar c ht'; rw [mul_zero] at he; convert! he using 2 with j; rw [Pi.smul_apply,smul_mul_assoc,scooted]
   | @add f g hf hg hh hu=> have he:=hh.sum hu; rw [add_zero] at he; convert! he using 2 with j; change (boost (H j) (Train.top i) ht B.K).average _ ((f j+g j)*_)= _; rw [add_mul,sun ((W) j) (boost (H j) (Train.top i) ht B.K) ((BondPalm H hf j).mul (anthemBond (hp j))) ((BondPalm H hg j).mul (anthemBond (hp j)))]; rfl
lemma arc_apt (h:4≤ i)(S:(j:ℕ)→ Lit (H j) Z b)(x:(i:ℕ)→ScriptJ (Libra.Keys G (Weir.Limb (H i))))(hk:Palm H d (fun i v=>(x i v).s))(hx:Tar H (fun i v=>(x i v).l))(hs:Z.gear=Train.top i)(hp:∀ i,StageLight.Track Z (U.M i))(ht:LocalRatio P)(hg:G.Simple) :
    (∃ c,Bloom U d (fun i=> ((S i).s.pay P (x i)).s) c) ∧ Fruit U d (fun i=> ((S i).s.pay P (x i)).l) 0 :=by -- power demand k etc
    have he j:=payoff (h:=h) (x j) (S j) hs (hp j) ht hg (BondPalm H hk j) (Tar_bond H hx j)
    constructor
    · simp_rw [fun i=> (he i).1]; exact fromCore (authorize H h hk)
    let Γ(j):= boost (G:=G) (H j) (Train.top i) h B.K; let g i:=(Γ i).average (W i) (fun y=>(x i y).l); let f i:= (Γ i).average (W i) ((fun y=>(x i y).s)*Shrew.Trill (anthem G (H i))); have hp:Fruit U d f 0:=indemnify H h hk hs hg hp; have hv:Fruit U d g 0:= (taxes H h hx).sap
    rw [show (fun i=> ((S i).s.pay P (x i)).l)=g+(fun i=> -1*f i) from funext fun i=>by rw [(he i).2];change _-f i=g i+ _; change g i-_= _;ring, ← add_zero (0:ℝ)]; exact hv.sum (by simpa only[mul_zero] using (Nestle.payScalar (-1) hp))
end YM.OPE.Prairies
