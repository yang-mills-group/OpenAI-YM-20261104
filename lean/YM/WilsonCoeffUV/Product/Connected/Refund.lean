import YM.WilsonCoeffUV.Product.Connected.BothSides
/-!
# Step reuse for aligned price domains
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
variable {p q:ProfileW}{D' t η K M s S δ:ℝ}
variable {b:ℕ}
def pearlB (u b:ℕ)(K D:ℝ):ℝ:= (D^b)⁻¹*(4*K)^u
lemma pearl_paid (p:SplitHill p q η K D'):0 ≤ pearlB u b K D':=by have he:=p.toll; have hv:=p.globe; unfold pearlB; positivity
lemma porchStave (G:ropes Cover α α)(P Q:Gen ℝ (Cloth α))(v:SplitHill p q η K D')(x:Rent p (u+b) (P (i+1)) A)(y:Rent q (u+b) (Q (j+1)) B)(g:dragCup Bank.terrain s C G)(t:0<s)(z:i+j=r): Ragtop 0 η u (rill G P Q r i j) (pegPrice i j*(pearlB u b K D' *(C*ceilPoly b s))*(B*A)):=by
   subst r; let T:=droplet i j α; let L:= pearlB u b K D'; let Z:= C*ceilPoly b s; let W:=pegPrice i j; have he:0≤Z:=mul_nonneg g.1 (ceilPoly_pos ..).le; have hp:0≤W:= by unfold W pegPrice; positivity
   let X (x:dock Cover α (j+1)):= quoteT q (u+b) x * ‖Q (j+1) x‖; let Y (x:dock Cover α (i+1)):=quoteT p (u+b) x*‖P (i+1) x‖
   let Q' x:=W*(L*Z)*(X (T x).1* Y (T x).2); refine budget_minor (cap_walk Q' _ T.symm (fun i=>by simp only [Q',T.apply_symm_apply]; rfl) (cap_scale (prod_cap y (cap_nn x) (fun _=> x)) (mul_nonneg hp (mul_nonneg (pearl_paid v) he)))) ?_ ?_
   · intro i; exact mul_nonneg (hedge_nn v.nonneg _) (norm_nonneg _)
   intro a; let V:= (T a).1; let U:= (T a).2; let G' := G (U 0) (V 0)
   have H : hedge 0 η u a.1*‖G'‖ ≤ L*quoteT p (u+b) U * quoteT q (u+b) V *Z:= spineR v a.1 a.2 G g t b u
   let Y':=‖P (i+1) U‖; let X':= ‖Q (j+1) V‖
   have hh:0≤ W*Y'*X':=by unfold X' Y'; positivity
   change hedge 0 η u a.1 * ‖rill G P Q _ _ _ a.1 a.2‖≤_; rw [rill_norm]; change _ * (W*‖G'‖ * Y' * X')≤ W*(L*Z)*(quoteT q (u+b) V*X'*(quoteT p (u+b) U*Y')); nlinarith only [mul_le_mul_of_nonneg_right H hh]
lemma porchPath (G H:ropes Cover α α)(P Q X Y:Gen ℝ (Cloth α))(v:SplitHill p q η K D')(f:PromX p (u+b) A δ (P (i+1)) (Q (i+1)))(g:PromX q (u+b) B δ (X (j+1)) (Y (j+1)))(hp:Ballast s C δ G H)(t:0<s)(z:i+j=r): YieldP 0 η u (3*pegPrice i j*(pearlB u b K D'*(C*ceilPoly b s))*(B*A)) δ (ruins (swivel (rill G P X r i j))) (ruins (swivel (rill H Q Y r i j))):=by
    subst r; have hx:= (porchStave G P X v f.paid g.paid hp.oneP t rfl).spun v.nonneg; have hv:= (porchStave H Q Y v f.feud g.feud hp.otherP t rfl).spun v.nonneg; have ht:=hx.collectR v.nonneg; let T:=pegPrice i j; let L:= pearlB u b K D'; let W:= C*ceilPoly b s; have h:T*(L*W)*(B*A)≤ 3*T*(L*W)*(B*A):=by have he:0≤ T*(L*W)*(B*A):=ht.C; nlinarith
    refine ⟨ht.more h,(hv.collectR v.nonneg).more h,?_⟩; rw [←hx.collect_minus hv v.nonneg, show swivel _-_=swivel (rill G P X (i+j) i j-rill H Q Y (i+j) i j) from ?_]
    · have h0:= porchStave (G-H) P X v f.paid g.paid hp.between t rfl
      have h1:= porchStave H (P-Q) X v f.dropR g.paid hp.otherP t rfl
      have h2:= porchStave H Q (X-Y) v f.feud g.dropR hp.otherP t rfl
      rw [show rill G P X (i+j) i j-rill H Q Y (i+j) i j= _ from ?_]; exact (((((h0.plus h1 v.nonneg).plus h2 v.nonneg).spun v.nonneg).collectR v.nonneg).more (le_of_eq (by ring)))
      funext x y; simp only [rill_spell,Pi.sub_apply, Matrix.sub_apply,Pi.add_apply, sub_mul,mul_sub,sub_smul,smul_sub]; abel
    funext x y; simp only [swivel,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_sub_distrib,smul_sub]
section
variable {I:Gear G}
structure TripG (e b u:ℕ)(I:Gear G) where
    R: Rally (e+1) 0 I
    p : ProfileW
    q : ProfileW
    K : ℝ
    D : ℝ
    η : ℝ
    fair : SplitHill p q η K D
    P : Bookend ℝ G
    Q : Bookend ℝ G
    U : Bookend ℝ G
    V : Bookend ℝ G
    A : ℝ
    B : ℝ
    meter i j:i≤e → PromX (fun x=>p (parentC I.patch.L x)) (u+b) A R.σ (P i j) (Q i j)
    measure i j:i≤e → PromX (fun x=>q (parentC I.patch.L x)) (u+b) B R.σ (U i j) (V i j)
abbrev sen (G:Gauge)(e b u):= (fun (I:Gear G) (T:TripG e b u I)=>T.R)
lemma TripG.ann (T:TripG e b u I): 0≤T.A:= ((T.meter 0 0 (Nat.zero_le _)).paid).C
lemma TripG.bnn (T:TripG e b u I):0≤T.B:= (T.measure 0 0 (Nat.zero_le _)).paid.C
abbrev rentP (j:ℕ)(X Z:(I:Gear G)→TripG e b u I→ Ten ℝ (Cloth (Helms I)) j):= Porch (fun _ v=>v.p) (xpos e (sen G e b u)) (dpos e (sen G e b u)) (fun _ v=>v.A) (u+b) X Z
abbrev rentQ (j:ℕ)(X Z:(I:Gear G)→TripG e b u I→ Ten ℝ (Cloth (Helms I)) j):= Porch (fun _ v=>v.q) (xpos e (sen G e b u)) (dpos e (sen G e b u)) (fun _ v=>v.B) (u+b) X Z
lemma rentPA (b u j:ℕ)(p:i≤e) (G:Gauge) (r:ℕ) : rentP (e:=e) (b:=b) (u:=u) (G:=G) r (fun I v=>Pcross I v.R.P v.P j i r) (fun I v=> Pcross I v.R.Q v.Q j i r):= sodRoots (T:=sen G e b u) (fun _ v=>v.p) (fun _ v=>v.A) (fun _ v=>v.P) (fun _ v=>v.Q) ⟨fun _ v=> v.fair.lipP,fun _I=>⟨fun v=>v.R.rich,fun v=>v.R.θ⟩,fun _ v=>v.ann⟩ p (fun j l h=>⟨0,fun I=> ⟨1,zero_le_one,fun v=>by rw [pow_zero,mul_one,one_mul]; exact v.meter l j h⟩⟩) p r j
lemma rentQA (b u j:ℕ)(p:i≤e) (G:Gauge) (r:ℕ) : rentQ (e:=e) (b:=b) (u:=u) (G:=G) r (fun I v=>Pcross I v.R.P v.U j i r) (fun I v=> Pcross I v.R.Q v.V j i r):= sodRoots (T:=sen G e b u) (fun _ v=>v.q) (fun _ v=>v.B) (fun _ v=>v.U) (fun _ v=>v.V) ⟨fun _ v=> v.fair.lipQ,fun _I=>⟨fun v=>v.R.rich,fun v=>v.R.θ⟩,fun _ v=>v.bnn⟩ p (fun j l h=>⟨0,fun I=> ⟨1,zero_le_one,fun v=>by rw [pow_zero,mul_one,one_mul]; exact v.measure l j h⟩⟩) p r j
abbrev TripG.plot (v:TripG e b u I):= pearlB u b v.K v.D * (v.A*v.B)
abbrev Spent {V:Gear G → Type*} (i:ℕ)(P Q:(I:Gear G)→ TripG e b u I → Ten ℝ (Cloth (V I)) i):= Fallow 0 u (xpos e (sen G e b u)) (dpos e (sen G e b u)) (fun _ v=>v.η) (fun _ v=>v.plot) P Q
lemma ChargePlot (G:Gauge)(e b u:ℕ): Meter (xpos e (sen G e b u)) (dpos e (sen G e b u)) (fun _ v=>v.η) (fun _ v=>v.plot):=⟨fun _I=>⟨fun v=>v.R.rich,fun v=>v.R.θ⟩,fun _I v=>v.fair.nonneg, fun _I v=>mul_nonneg (pearl_paid v.fair) (mul_nonneg v.ann v.bnn)⟩
lemma Spent.wings (i j k:ℕ)(hv:j≤e) (R Q:(I:Gear G)→ TripG e b u I→ ropes Cover (Helms I) (Helms I))(p:∀ i j,Ballast i.σ i.D j.R.σ (R i j) (Q i j)) : Spent k (fun I v=> Soil.paintC (R I v) (Pcross I v.R.P v.P) (Pcross I v.R.P v.U) i j k) (fun I v=> Soil.paintC (Q I v) (Pcross I v.R.Q v.Q) (Pcross I v.R.Q v.V) i j k):=by
   simp_rw [Soil.paintC,Finset.sum_apply]; apply Fallow.sum _ (ChargePlot ..); intro n hn; apply Fallow.sum _ (ChargePlot ..); intro l hl; have ht:=Finset.mem_antidiagonal.mp hl; simp_rw [rondel]; apply Fallow.sum _ (ChargePlot ..); intro t hp
   obtain ⟨a,H⟩:= rentPA b u n.1 (show l.1≤e from by omega) G (t.1+1); obtain ⟨d,F⟩:= rentQA b u n.2 (show l.2≤ e from by omega) G (t.2+1); refine ⟨a+d,fun I=>?_⟩; obtain ⟨A,h,f⟩:= H I; obtain ⟨B,g,h'⟩:= F I; let S:=ceilPoly b I.σ
   refine ⟨3*pegPrice t.1 t.2*(I.D*S)*A*B,by have hh:=zero_le_one.trans I.bill_nn; have hs:0≤S:=(ceilPoly_pos ..).le; unfold pegPrice; positivity,fun v=>?_⟩; rw [pow_add]; convert! porchPath _ _ _ _ _ _ v.fair (f v) (h' v) (p I v) I.price (Finset.mem_antidiagonal.mp hp) using 1; unfold TripG.plot S; ring
abbrev boilingJ (I:Gear G)(R:Stand I)(P Q:Bookend ℝ G):= boilC I.patch I.kernel I.angle R.R R.Q R.page P Q
lemma burgeon (G:Gauge)(e u b:ℕ) (hv:i≤e)(k r:ℕ) : Spent (G:=G) (e:=e) (u:=u) (b:=b) r (fun I v=>boilingJ I v.R.P v.P v.U k i r) (fun I v=> boilingJ I v.R.Q v.Q v.V k i r):=by
   induction k using Nat.strong_induction_on generalizing r i with
   | h k ih=>
      cases k with
      | zero=> simp only [boilingJ,boilC,gorge]; exact Fallow.zero
      | succ k=>
        let T:= TripG e b u (G:=G); let X (I:Gear G)(v:T I):= v.R.P.payMat; let Z (I:Gear G)(v:T I):=v.R.Q.payMat; let P (I:Gear G)(v:T I):= boilingJ I v.R.P v.P v.U; let Q (I:Gear G)(v:T I):= boilingJ I v.R.Q v.Q v.V
        have hu n (h:n≤k) l (x:l≤e) r: Spent r (fun I v=> P I v n l r) (fun I v=>Q I v n l r):= ih n (by omega) x r
        have hp (i:Gear G) (v:T i):Ballast i.σ i.D v.R.σ (X i v) (Z i v):= (pm_rate v.R).mono i.holds.le
        have ht:= Spent.wings k i r hv X Z hp; let A' I v:=(X I v).transpose; let B' I v:=(Z I v).transpose; have he I v:= Cosmos.BankT (hp I v)
        have hd:= Spent.wings k i r hv A' B' he; let K:=sen G e b u
        have hf (X Z) (hx:∀ i j,Ballast i.σ i.D (dpos e (sen G e b u) i j) (X i j) (Z i j)):= meadow (T:=K) (W:=P) (Z:=Q) (k:=k) 0 _ _ (ChargePlot G e b u) (fun i j=> j.fair.year) hv (fun n h j p r=>hu n h j (p.le.trans hv) r) X Z hx r
        obtain ⟨d,H⟩:= hu k le_rfl i hv (r+2)
        have hy : Spent r (fun I v=> rime (X I v) (P I v k i) r) (fun I v=> rime (Z I v) (Q I v k i) r):=by
            refine ⟨d,fun I=>?_⟩; obtain ⟨A,h,f⟩:=H I; have hb := zero_le_one.trans I.bill_nn
            refine ⟨2*I.D*A*fareV r,by unfold fareV; positivity,fun v=>?_⟩; let V:=X I v; let Z':=Z I v; let z:=hp I v
            have he:= (f v).rimeX v.fair.nonneg V Z' hb z.between.1 (herb_pt z.oneP I.price.le) (herb_pt z.otherP I.price.le) (herb_pt z.between I.price.le); convert! he using 1; ring
        simp only [boilingJ,boilC,riseG,Pi.smul_apply,inertial]; exact Fallow.st (Bank.Slate.one (P:=fun _ => ((k+1:ℕ):ℝ)⁻¹) (ChargePlot G e b u).shine) ((((hy.plus (hf _ _ hp) (ChargePlot ..)).plus (hf _ _ he) (ChargePlot ..)).plus ht (ChargePlot ..)).plus hd (ChargePlot ..)) (ChargePlot ..)
end
end YM.WilsonCoeffUV.Mer
