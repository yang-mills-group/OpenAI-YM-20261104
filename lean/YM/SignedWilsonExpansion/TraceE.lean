import YM.SignedWilsonExpansion.Bubble
namespace YM.SignedWilsonExpansion.TraceE
/-! # The explicit one-loop internal expression through d=4, at MOMENTUM-heat time t. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView
open scoped Classical Topology ContDiff BigOperators
open Energy (plane leg firstE)
variable {G:Gauge} {a b c d i j u v l m:Axis} {A B Cc T:G.ColorIndex}
  {h:ℝ→ℝ}{p q r k x y S:FourP}{t:ℝ}
local notation "Ψ"=>field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
local notation "Y" => yMark a b
local notation "g" => Canvas.triple G
local notation "X" => firstE a b G 0

abbrev root (h:ℝ→ℝ) : Law G:= B₂ G 0+Canvas.quad G h g g
abbrev peak (a b:Axis) (t:ℝ) (G:Gauge): Law G:= MarkTop.charged (Energy.called a b G) ( firstE a b G 0 ) t

lemma root_s : Symm Ψ (root h: Law G):= ( B₂_P G 0|>.sym ).add ( ( tree_sym (Shells.closure G h) (F:=g) (H:=g) (fund_one G 0|>.sym) (fund_one G 0|>.sym) ).smul _ )
lemma paint_neg : Bubble.paint h (-p) a b i= -Bubble.paint h p a b i:= by unfold Bubble.paint; rw [leg_neg,Landau.sq_neg]; ring
abbrev legQ (h:ℝ→ℝ) (k:FourP) (u:Axis) (i j:Axis) (p q:FourP) (a b:Axis):ℝ:=
    ∑ α:Axis, strength a b h (-k-(p+q)) α * body h u α i j k p (-k-(p+q)) q
def stem (h:ℝ→ℝ) (k:FourP) (u v:Axis) (i j:Axis) (p q:FourP) (a b:Axis) : ℝ:=
      -legQ h k u i j p q a b * leg a b v k

lemma changeβ : let w:= [W i B p,W j B q]
     pick (p+q) a b h (W v A (-k)) w ( D (W u A k) (root h) )= ↑(stem h k u v i j p q a b)*twinColor A B := by
    dsimp only; rw [picked]; unfold stem legQ; simp_rw [ at_D,leg_neg, root, cloud4 (p:=p) (q:=q) (r:=-k-(p+q)) (k:=k) (by abel) ]; push_cast; simp_rw [← Finset.sum_neg_distrib,Finset.sum_mul]; apply Finset.sum_congr rfl; intro α _; ring
lemma changeα : let w:= [W i B p,W j B q]
    pick (p+q) a b h (W u A k) (W v A (-k)::w) ( root h )= ↑(stem h (-k) v u i j p q a b)*twinColor A B := by
    intro w; have he (F:Law G) (hp:Symm Ψ F): pick (p+q) a b h (W u A k) (W v A (-k)::w) F=pick (p+q) a b h (W u A k) w ( D (W v A (-k)) F ):= by
        simp_rw [picked, at_D]; refine Finset.sum_congr rfl fun α _=>?_ ; let x:=W α A (k-(p+q)); let i:= W v A (-k); rw [ show F (x::i::w)=F (i::x::w) from (hp [] x i w).trans (one_mul _) ]; -- `rw` pattern`i`
    have hv:= changeβ (a:=a) (b:=b) (h:=h) (A:=A) (B:=B) (i:=i) (j:=j) (p:=p) (q:=q) (k:=-k) (u:=v) (v:=u); dsimp only at hv; rw [neg_neg] at hv; exact (he _ root_s).trans hv

def exterior (S:FourP) (x y:Lane4 G) (h:ℝ→ℝ) (a b:Axis) (w:Legs (Lane4 G)):ℂ:= changeF S a b h ( D y ( D x (root h))) w
local notation "Σg"=> Branch G Axis
lemma exterior_thin (f:ℝ→ℝ) (k:FourP) (w:Legs (Lane4 G)) (hn:S=net w) : changeF S a b h (trc (lineL G f) k (root h)) w=∑ (i:Σg),∑ (j:Σg),lineL G f i j k * exterior S (i,k) (j,-k) h a b w:= by unfold Flux.trc; simp only [ exterior,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul ]; rfl

lemma gauge_diagonal :
    let w:= [W i B p,W j B q]; let α:=W u A k; let β:=W v A (-k)
    peak a b t G (α::β::w)- exterior (p+q) α β (amp t) a b w=
       ↑(leafPrice (amp t) a b i j u v p q k (p+q) + leafPrice (amp t) a b i j v u p q (-k) (p+q)+stem (amp t) k u v i j p q a b+stem (amp t) (-k) v u i j p q a b)*twinColor A B := by
    intro w α β; rw [ peak, decision (p+q) _ _ (by simp [α,β,W,qnote,w,net]), Walk.chosen,Walk.chosen ]; dsimp only
    unfold exterior; obtain hl := leaf_cost (a:=a) (b:=b) (h:=amp t) (A:=A) (B:=B) (k:=k) (i:=i) (u:=u) (j:=j) (v:=v) (p:=p) (q:=q) (p+q)
    push_cast at hl ⊢
    let F':= root (G:=G) (amp t); rw [
        show pick (p+q) a b (amp t) α (β::w) ( (B₂ G 0)+ _ )= _ from changeα (a:=a) (b:=b) (A:=A) (B:=B) (k:=k) (i:=i) (u:=u) (j:=j) (v:=v) (p:=p) (q:=q), -- defeq
        show pick (p+q) a b (amp t) β w (D α ( (B₂ G 0)+ _ ))= _ from changeβ (a:=a) (b:=b) (A:=A) (B:=B) (k:=k) (i:=i) (u:=u) (j:=j) (v:=v) (p:=p) (q:=q) ];
    unfold α β w root; linear_combination hl
lemma ghost_diagonal (α β:Lane4 G) (h₁:wing α) (h₂:wing β) (he:α.1.2=β.1.2) (hv:α.2+β.2=0) :
    let w:= [W i B p,W j B q]
    peak a b t G (α::β::w)- exterior (p+q) α β (amp t) a b w=0:= by
    dsimp only; rw [ peak, decision (p+q) _ _ (by rw [net_cons,net_cons, ← add_assoc,hv,zero_add]; simp [net,W,qnote]), ghost_I h₁ h₂ he,ghost_T h₁ h₂ he,Walk.chosen,Walk.chosen ]
    dsimp only; rw [ unused _ _ (side h₁), unused _ _ (side h₂),add_zero,zero_add,zero_add,zero_add ]; exact sub_self _

def complete (h:ℝ→ℝ) (a b:Axis) (p q:FourP) (i j:Axis) (k:FourP):ℝ:=
    (∑ u:Axis,∑ v:Axis, precision u v k * leafPrice h a b i j u v p q k (p+q))
       +∑ u:Axis,∑ α:Axis,4*k.sq*leg a b u k* Bubble.paint h (k+(p+q)) a b α * body h u α i j k p (-k-(p+q)) q
lemma finish (f:ℝ→ℝ): (∑ u:Axis, ∑ v:Axis,bond f k u v * ( leafPrice h a b i j u v p q k (p+q)+stem h k u v i j p q a b))= f k.sq*complete h a b p q i j k:= by
    unfold complete; rw [mul_add]; simp only [ mul_add, Finset.sum_add_distrib ]; congr 1
    · simp_rw [bond, mul_assoc,Finset.mul_sum]
    unfold stem legQ; simp_rw [mul_comm _ (leg _ _ _ _)]; -- rotates
    have he: -k-(p+q)= -(k+(p+q)):=by abel
    simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    simp_rw [he,painted,paint_neg]; --
    conv_lhs=> enter [2,z]; rw [← mul_assoc] -- arg? Fin.sum
    rw [← Finset.sum_mul, projection f]; simp_rw [← Finset.sum_neg_distrib, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

def price (h:ℝ→ℝ)(p q:FourP)(i j:Axis)(u v:Axis)(a b:Axis)(k:FourP):ℝ:= leafPrice h a b i j u v p q k (p+q)+stem h k u v i j p q a b
lemma both (f:ℝ→ℝ) :
   ∑ u:Axis,∑ v:Axis, bond f k u v*( price h p q i j u v a b k + price h p q i j v u a b (-k))=f k.sq * ( complete h a b p q i j k+complete h a b p q i j (-k) ):= by
     have he v u: bond f k v u=bond f (-k) u v:= by rw [ bond_neg ]; unfold bond; rw [realK]
     simp only [ mul_add,Finset.sum_add_distrib ]; unfold price; rw [ finish ]
     congr 1; conv_lhs=>rw [Finset.sum_comm]
     calc
       _ = f (Momentum.sq (-k)) * complete h a b p q i j (-k):= by nth_rw 1 [← finish]; apply Finset.sum_congr rfl; intro u _; refine Finset.sum_congr rfl fun v _=>?_ ; rw [ he ]
       _=_ := by rw [Landau.sq_neg]

lemma shapeLoop (f:ℝ→ℝ) (A:G.ColorIndex) :
    let w:=[W i B p, W j B q]
    let K (α β:Branch G Axis):=peak a b t G ((α,k)::(β,-k)::w) - exterior (p+q) (α,k) (β,-k) (amp t) a b w
    ((∑ u:Axis,∑ v:Axis, ↑(bond f k u v)* K (W₀ u A) (W₀ v A))+
          (∑ u:Axis, Area.tail2 f k u * K (U₀ u A) (C₀ A))+(∑ u:Axis,Area.tail2 f k u * K (C₀ A) (U₀ u A)))=
    (↑( f k.sq * ( complete (amp t) a b p q i j k + complete (amp t) a b p q i j (-k)) ):ℂ)*twinColor A B:= by
    intro w K
    have hz (x y:Branch G Axis)(hA:parity x=true)(hB:parity y=true)(he:x.2=y.2): K x y =0:=ghost_diagonal (a:=a) (b:=b) (t:=t) (B:=B) (p:=p) (q:=q) (i:=i) (j:=j) (x,k) (y,-k) hA hB he (add_neg_cancel _)
    have ht (u v:Axis): K (W₀ u A) ( W₀ v A )=(↑( price (amp t) p q i j u v a b k + price (amp t) p q i j v u a b (-k)):ℂ)*twinColor A B:= by unfold K; rw [ show ( W₀ u A,k )=W u A k from rfl, show (W₀ v A,-k)= W v A (-k) from rfl ]; dsimp only [w]; rw [gauge_diagonal]; unfold price; push_cast; ring
    simp_rw [ ht, hz (U₀ _ _) (C₀ _) rfl rfl rfl, hz (C₀ _) ( U₀ _ _ ) rfl rfl rfl, mul_zero, Finset.sum_const_zero,add_zero,← both f ]; push_cast; simp_rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; ring

lemma formula (f:ℝ→ℝ)(simple:G.Simple) : trc (lineL G f) k (peak a b t G) [ W i B p,W j B q ]=
    ↑(G.casimir*f k.sq *( complete (amp t) a b p q i j k + complete (amp t) a b p q i j (-k))) + changeF (p+q) a b (amp t) (trc (lineL G f) k (root (amp t))) [ W i B p,W j B q ] := by
    rw [ ← sub_eq_iff_eq_add, exterior_thin f k _ (by simp [net,W,qnote]), at_trc ]; simp only [ ← Finset.sum_sub_distrib, ← mul_sub ]; rw [ starLine ];
    simp_rw [ shapeLoop f ]; rw [← Finset.mul_sum, SumColor simple]; push_cast; ring

end
end YM.SignedWilsonExpansion.TraceE
