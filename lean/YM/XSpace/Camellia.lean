import YM.XSpace.Flute
/-!
# Stake of the second-slot window and lead coefficient on scenes
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Gland Chart2 Octave Season Lattice MvPolynomial Chiral Graph3 Player Relief Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{W: Initialize G}{ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{C:Shade.Cut}{i j k:ℕ}
abbrev dual (A B:Line G) : Module.Dual ℂ (Stamp G):= (peek G).toLinearMap ∘ₗ Ξ A ∘ₗ Ξ B
def pair (A B: Player W)(g:G.Simple)(x y z:Cover) : Module.Dual ℂ (Stamp G):= dual (A.ask g y) (B.ask g z) ∘ₗ (Trace.volume x).toLinearMap
variable (P Q:Player W)(g:G.Simple)(x y z:Cover)
lemma pair_at (V:Stamp G): pair P Q g x y z V= peek G (Ξ (P.ask g y) (Ξ (Q.ask g z) (Trace.volume x V))):=rfl
lemma twons (V Y:Line G): pair P Q g x y z (harp V*harp Y)= collation V (P.origin g) x y * collation Y (Q.origin g) x z+ collation Y (P.origin g) x y*collation V (Q.origin g) x z:=by
  rw [pair_at,map_mul (Trace.volume x),Trace.rings,Trace.rings]; simp only [ξ_mul,map_add,map_mul,ξ_harp,ξ_zero,mul_zero,zero_mul,peek_C,add_zero,zero_add]; unfold collation; rw [Player.ask,Player.ask,cable,cable]; unfold Player.origin; ring
lemma twain (V Y:Axis) (a b:G.ColorIndex) : pair P Q g x y z (av V a * av Y b)=(↑(P.M g V (x-y)*χ P.color a*(Q.M g Y (x-z)* χ Q.color b) + P.M g Y (x-y)*χ P.color b*(Q.M g V (x-z)*χ Q.color a)):ℂ):=by
  rw [pair_at,map_mul (Trace.volume x),arrow,arrow, ← show F2 G (harp _*harp _) (harp _ * harp _)=_ from ζ_two (Q.ask g z) (P.ask g y) (harp (needle ((x,V),a))*harp (needle ((x,Y),b))), ζ_pair]; unfold col; change (handshake₀ _ _ _ _ _ _:ℂ) * (handshake₀ _ _ _ _ _ _:ℂ)+ (handshake₀ _ _ _ _ _ _:ℂ)*(handshake₀ _ _ _ _ _ _:ℂ)=_; simp_rw [handshake_pin]; push_cast; ring
local notation "brλ" => br
local notation "qZ"=> q
abbrev print (σ:Bool)(i:Name G) (u v:Axis):= q σ i.1 u v * (P.M g u (x-y)* Q.M g v (x-z))
abbrev kernel (σ:Bool)(u:E4)(v b:E4)(i:Name G): ℂ:= ↑(br i.2 P.color Q.color * ∑ j:Axis,∑ k:Axis,q σ i.1 j k * (P.gCost j (u-v)*Q.gCost k (u-b)))
lemma reel (u v:Axis)(a:G.ColorIndex): pair P Q g x y z (mode u v a)= (↑(br a P.color Q.color * P.M g u (x-y)*Q.M g v (x-z)+ br a Q.color P.color * P.M g v (x-y)*Q.M g u (x-z)):ℂ):=by
  unfold mode Stk; simp_rw [_root_.map_sum,map_smul]; change (∑ j:G.ColorIndex,∑ k:G.ColorIndex,(br a j k:ℂ)*pair P Q g x y z (av u j*av v k))=_; simp_rw [twain, ← Complex.ofReal_mul, ← Complex.ofReal_sum]; congr 1; simp_rw [mul_add,Finset.sum_add_distrib, χ, mul_ite,ite_mul, mul_zero,zero_mul,mul_one]; simp; ring
lemma needlework (σ:Bool)(i:Name G): pair P Q g x y z (stance σ i)= ↑(br i.2 P.color Q.color * ∑ u:Axis,∑ v:Axis, print P Q g x y z σ i u v):=by -- i.color typo
  let f:=print P Q g x y z σ i; unfold stance; rw [map_sum,Finset.sum_comm (t:=(Finset.univ:Finset Axis)), order_poly f (fun i' => by simp [f,print,qdiag]),Finset.mul_sum, Complex.ofReal_sum]; refine Finset.sum_congr rfl fun p _=>?_ ; rw [map_smul,reel, beamD]; let u:=six p; let v:=endr p; let w i:=P.M g i (x-y); let w' i:=Q.M g i (x-z); change (q σ i.1 u v:ℂ)* ↑(br i.2 P.color Q.color * w u*w' v+br i.2 Q.color P.color*w v*w' u)=(↑(br i.2 P.color Q.color * (q σ i.1 u v * (w u*w' v) + q σ i.1 v u * (w v*w' u))):ℂ); rw [← Complex.ofReal_mul,chosen_sqrt2 σ i.1 u v,br_swap i.2 Q.color P.color]; congr 1; ring
-- cost even both different depths at same anchor (x distinct though).
variable {x y z:ι→Cover}
private def boat (s:Stage L a)(h:distFee L a (fun i=>x i-y i))(H:distFee L a (fun i=>x i-z i))(n:ℕ): Levee G where
 carrier := {A| funds L a n (fun i=> pair P Q g (x i) (y i) (z i) A)}
 zero_mem' := (isBigO_zero ..).congr (fun i=> (map_zero _).symm) (fun _=>rfl)
 add_mem' := by intro A B h H; simp_rw [mem_setOf,map_add]; exact IsBigO.add h H
 smul_mem' := by intro k A h; simp_rw [mem_setOf,map_smul,smul_eq_mul]; exact IsBigO.const_mul_left h k
lemma due (s:Stage L a)(h:distFee L a (fun i=> x i-y i))(H:distFee L a (fun i=>x i-z i)){A:Stamp G}(hh:A∈ Duo G i j): funds L a (6+i+j) (fun i=> pair P Q g (x i) (y i) (z i) A):= by
  change A∈ boat _ _ g s h H _; refine through _ (fun w hw v hv=> ?_) hh; change funds L a _ _; simp_rw [twons]
  have ht:= gowns (fare_stake s w (P.origin g) hw (P.visit g) h) (fare_stake s v (Q.origin g) hv (Q.visit g) H); have hh:=gowns (fare_stake s v (P.origin g) hv (P.visit g) h) (fare_stake s w (Q.origin g) hw (Q.visit g) H); rw [show 2+i+1+(2+j+1) = 6+i+j by omega] at ht; rw [show 2+j+1+(2+i+1)=6+i+j by omega] at hh; exact IsBigO.add ht hh
variable {u v b:E4} (T:Captain C L a x y z u v b)
include T in
lemma ask_pair (σ:Bool)(i:Name G): Named L a 6 (fun w=> pair P Q g (x w) (y w) (z w) (stance σ i)) (kernel P Q σ u v b i):=by
  simp_rw [needlework]; apply Named.coe; let f:=br i.2 P.color Q.color; have he(j k:Axis): Tendsto (fun l => (a l)⁻¹^6*print P Q g (x l) (y l) (z l) σ i j k) L (𝓝 (q σ i.1 j k*(P.gCost j (u-v)*Q.gCost k (u-b)))):=by
    refine (((P.credited g T j).mul (Q.credited g T.hop.turn k)).const_mul _).congr fun w=>?_ ; unfold print; ring
  apply Tendsto.congr _ ((tendsto_finsetSum _ (fun j (_:j∈Finset.univ)=> tendsto_finsetSum _ (fun k (_:k∈Finset.univ)=>he j k))).const_mul f); intro w; dsimp only; simp_rw [← Finset.mul_sum]; exact mul_left_comm .. 
include T in
lemma projects (J:Player W): Named L a 6 (fun w=> pair P Q g (x w) (y w) (z w) (brace J.size J.σ J.elem 0)) (kernel P Q J.σ u v b J.elem):=by
  refine (ask_pair P Q g T J.σ J.elem).wallet (Named.low ?_ T.led); simp_rw [← map_sub]; refine minute T.led (due P Q g T.led T.sec T.grant.xz (i:=1) (j:=0) ?_) (?_) -- nf ; swap
  · rw [← fare_lit g J.size J.hr]; exact hollow (brace_degree J.size J.σ J.elem 0)
  norm_num
end YM.XSpace.Finale
