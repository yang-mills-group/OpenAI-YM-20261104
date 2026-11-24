import YM.SignedWilsonExpansion.Energy
import YM.FVA2.Lambda.Cherry
namespace YM.SignedWilsonExpansion.Walk
/-! Mark potential and its high tensor readings. Works with the same cubic
and kinetic as in the FVA2.Lambda continuum proof. In particular no weights
hidden in the choice of color/polarization of the test. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area
open HighScale HighRank TreeLine TreeView
open Energy (plane firstE leg)
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {h:ℝ→ℝ} {t:ℝ}
local notation "Ψ"=>field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
abbrev lineL (G:Gauge)(h:ℝ→ℝ): Line G:= Shells.link G h
abbrev bond (h:ℝ→ℝ)(p:FourP)(a b:Axis) : ℝ:= h p.sq * precision a b p
abbrev R (G:Gauge)(h:ℝ→ℝ)(F H:Law G)(l r:Legs (Lane4 G)):= Flux.attaches parity (lineL G h) F H l r
lemma starLine (h:ℝ→ℝ)(p:FourP)(F:Branch G Axis→Branch G Axis→ℂ) :
    (∑ i,∑ j, lineL G h i j p*F i j) =
       ∑ k:G.ColorIndex,( (∑ a:Axis,∑ b:Axis, ↑(bond h p a b)* F (W₀ a k) ( W₀ b k ))+
          (∑ a:Axis, tail2 h p a * F (U₀ a k) (C₀ k))+(∑ a:Axis,tail2 h p a * F (C₀ k) (U₀ a k))):= Area.paircol h p F
lemma chart (F H:Law G)(l r:Legs (Lane4 G)): R G h F H l r=2* Bead.attach h F H l r:= by
    rw [ show R _ _ _ _ _ _=_ from convertR (F:=F) (H:=H) (l:=l) (r:=r) (Shells.flipped G h) ]; unfold Bead.attach Bead.summit radius; simp_rw [Finset.mul_sum,mul_assoc]

lemma ampL : TreeLine.chi G t=lineL G (amp t):=by
    funext i j p; unfold lineL Shells.link Landau.choir TreeLine.chi BLine Landau.choir; by_cases he:i.2=j.2
    swap; · rw [if_neg he, if_neg he]; exact smul_zero ..
    rw [if_pos he, if_pos he]; rcases i with ⟨⟨_|i,_|_⟩,a⟩<;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> (simp [TreeLine.base,Shells.MK, Complex.real_smul] <;> ring)
lemma dotL : PlanetD G t=lineL G (Shells.hot t):=Shells.sweep G t
lemma quad_tree (F H:Law G)(w:Legs (Lane4 G)): Flux.tree parity (lineL G h) F H w=2*Canvas.quad G h F H w:= by unfold Canvas.quad; rw [Pi.smul_apply, smul_eq_mul,mul_inv_cancel_left₀ (show (2:ℂ)≠0 from by norm_num)]

variable {a b c d i j k l:Axis} {A B Cc D : G.ColorIndex}
variable {p q r s:FourP}
lemma projection (D:ℝ→ℝ) :
    ∑ i:Axis,bond D p j i *leg a b i p = p.sq* D p.sq *leg a b j p:= by
    simp_rw [bond,mul_assoc,← Finset.mul_sum]
    have he : ∑ i:Axis,precision j i p *leg a b i p=p.sq*leg a b j p:=by
        simp only [leg,mul_sub,mul_ite,Finset.sum_sub_distrib,mul_zero]; simp; unfold precision Landau.delta; split_ifs <;> ring
    rw [he]; ring
lemma progress : (fun p:FourP=> (∑ i:Axis,leg a b i p*p i))=0:= by ext p; simp [leg,ite_mul,Finset.sum_sub_distrib,sub_mul]; ring
lemma leg_neg : leg a b i (-p)= -leg a b i p:=by unfold leg; split_ifs <;> simp <;> abel

local notation "N" => plane a b G 0
local notation "E3" => firstE a b G 0
local notation "T" => B₂ G 0
local notation "J" => Canvas.triple G
local notation "X" => Slice.rib

lemma cub_eq : BulkTop.cub G=J:= by rw [Canvas.triple,pulse1]

-- proof currency from leg rank/permutation and curvature witnesses.
def vector (i:Lane4 G): Prop := ∃ a:Axis,i.1.1=gauge a
lemma vector_A (l:Axis)(i:G.ColorIndex)(p:FourP): vector (W l i p) := ⟨l,rfl⟩
lemma vector_ex (w:Lane4 G)(h:vector w) : ∃ (a:Axis)(k:G.ColorIndex)(p:FourP),w=W a k p:= by obtain ⟨a,ha⟩:=h; exact ⟨a,w.1.2,w.2,by ext <;> simp [W,qnote,ha] ⟩
def gaugeOnly (F:Law G) : Prop:= ∀ w, (∃ i∈w, ¬vector i) → F w=0
lemma only0 : gaugeOnly (0:Law G):=fun _ _=>rfl
lemma gaugeOnly.add {F H:Law G}(h:gaugeOnly F)(he:gaugeOnly H): gaugeOnly (F+H):= fun w hw=> by rw [Pi.add_apply,h w hw,he w hw,add_zero]
lemma gaugeOnly.smul {F:Law G}(h:gaugeOnly F)(c:ℂ): gaugeOnly (c • F):= fun w hw=> by rw [Pi.smul_apply,h w hw,smul_zero]
lemma gaugeOnly.sum {ι:Type}(S: Finset ι) {x:ι→Law G} (h:∀ i∈S,gaugeOnly (x i)): gaugeOnly (∑ i∈S,x i):=by intro w he; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun _ h' => h _ h' _ he
lemma gaugeOnly.product {F H:Law G}(h:gaugeOnly F)(ht:gaugeOnly H): gaugeOnly (Koszul.product Ψ F H):=by
    rintro w ⟨i,hi,hv⟩; rw [scattered]; apply Eq.trans (scatter_congr Ψ w _ (fun _ _=>(0:ℂ)) ?_) (map_zero (allocate Ψ w)); intro l r hr; have he:= (split_perm hr).mem_iff.mpr hi; rcases List.mem_append.mp he with hp|hp; rw [h l ⟨_,hp,hv⟩,zero_mul]; rw [ht r ⟨_,hp,hv⟩,mul_zero]
lemma leaf_g (a:Axis)(i:G.ColorIndex) : gaugeOnly ( Motif.A 0 G a i ):= by
    rintro (_|⟨x,_|xs⟩) ⟨j,hq,he⟩; · simp at hq
    · rw [List.mem_singleton] at hq; subst j; exact if_neg (fun h : x.1= Motif.at_g (n:=0) a i=> he (show vector x from ⟨a,h ▸ rfl⟩))
    rfl
lemma curlG (a b:Axis)(i:G.ColorIndex):gaugeOnly ( Motif.F₀ (n:=0) a b i):= by
   intro w hp; unfold Motif.F₀; simp_rw [axisP,Pi.sub_apply,lock,rowP,moon] -- inspect
   rw [leaf_g b i w hp,leaf_g a i w hp]; simp
lemma quillG (a b:Axis)(i:G.ColorIndex):gaugeOnly ( quill (n:=0) a b i):= by
   rw [quill,chew]; exact gaugeOnly.sum _ (fun _ _=> gaugeOnly.sum _ fun j _=> ((leaf_g a _).product (leaf_g b j)).smul _)
lemma plane_g {a b:Axis}:gaugeOnly (plane a b G 0):= gaugeOnly.sum _ fun i _=> (curlG a b i).product (curlG a b i)
lemma first_g {a b:Axis}:gaugeOnly (firstE a b G 0):= gaugeOnly.add (gaugeOnly.sum _ fun i _=> (curlG a b i).product (quillG a b i)) (gaugeOnly.sum _ fun i _=>(quillG a b i).product (curlG a b i))
lemma top_g : gaugeOnly T:= gaugeOnly.smul (gaugeOnly.sum _ fun i _=> gaugeOnly.sum _ fun j _=> gaugeOnly.sum _ fun k _=>(quillG i j k).product (quillG i j k)) _

lemma ranked_N : Book.rank 2 N:= BulkTop.strictr (rank_α (n:=0) a b) (rank_α (n:=0) a b) -- fix punctuation
lemma curl : F₀ (n:=0) a b A [W i B p]= if B=A then Complex.I*(leg a b i p:ℂ) else 0:= by
    obtain h:= f_ref (n:=0) a b i A B p; simp_rw [Landau.delta,eq_comm (a:=a) (b:=i),eq_comm (a:=b) (b:=i)] at h; exact h
lemma peel : plane a b G 0 [W i A p, W j B q]= if A=B then ↑((-2:ℝ)*leg a b i p * leg a b j q) else 0:= by
    unfold plane sume; simp only [ Finset.sum_apply ]; simp_rw [ bite, pairv (F:=F₀ _ _ _) (H:=F₀ _ _ _) (rank_α _ _ _) (rank_α _ _ _) ]; -- parsing
    simp only [curl, show Ψ (W i A p)=false from rfl, cross_false, one_mul ]; rw [ Finset.sum_eq_single A ]
    · by_cases he : A=B
      · subst B; simp [show chair 0 a=a from rfl, show chair 0 b=b from rfl]; linear_combination 2* (leg a b i p:ℂ)*(leg a b j q:ℂ)*Complex.I_sq
      simp [he,Ne.symm he]
    · intro x _ hx; simp [Ne.symm hx]
    simp
-- compute Y 3 and H0 tensor. orientation `Slice.foot`
abbrev play (a b i j:Axis): ℝ:= Slice.delta i a*Slice.delta j b-Slice.delta i b*Slice.delta j a
def yMark (a b i j k:Axis)(p q r:FourP):ℝ:= 2*(leg a b i p*play a b j k + leg a b j q*play a b k i + leg a b k r*play a b i j)
lemma quill_w : quill (n:=0) a b A [W i B p,W j Cc q]= rune B Cc A *(play a b i j:ℂ):= by
  change quill _ _ _ [Slice.EM _ _ _, Slice.EM _ _ _]=_
  rw [Slice.foot]; simp only [play, Slice.delta]; split_ifs <;> norm_num
lemma quill_w1 : ∑ i':G.ColorIndex, F₀ (n:=0) a b i' [W i A p] * quill (n:=0) a b i' [W j B q,W k Cc r]
      = Complex.I*rune B Cc A *((leg a b i p*play a b j k:ℝ):ℂ) := by
  simp_rw [curl,quill_w,ite_mul]; simp; ring
lemma play_turn (a b x y:Axis): play a b x y= -play a b y x:= by unfold play; ring
lemma first_A : firstE a b G 0 [W i A p, W j B q,W k Cc r]= Complex.I*rune A B Cc *( yMark a b i j k p q r:ℂ ):= by
    have he i' : bite 0 G (quill (n:=0) a b i') ( F₀ (n:=0) a b i' )= bite 0 G ( F₀ (n:=0) a b i' ) (quill (n:=0) a b i'):= ((Slice.rightR _ _ _).central _ ).symm
    let w:Legs (Lane4 G):= [W i A p, W j B q,W k Cc r]; change (sume (G:=G) (F₀ (n:=0) a b) (quill a b) w + sume (G:=G) (quill a b) (F₀ (n:=0) a b) w)=_; dsimp only [w]
    rw [show sume (G:=G) (quill (n:=0) a b) (F₀ (n:=0) a b)=sume (F₀ a b) (quill a b) from Finset.sum_congr rfl (fun i _=> he i)]
    have hx(i':G.ColorIndex):= Slice.twice (F₀ (n:=0) a b i') (quill (n:=0) a b i') (rank_α (n:=0) a b i')  (W i A p) (W j B q) (W k Cc r) rfl rfl rfl
    unfold sume; simp only [Finset.sum_apply,hx, Finset.sum_add_distrib]; rw [quill_w1,quill_w1,quill_w1]; rw [← r_clock A B Cc, r_ortho A Cc B,r_clock Cc A B]; unfold yMark; rw [play_turn a b i k]; push_cast; ring

lemma square4 (P:Law G)(h:Book.rank 2 P)(x y z t:Lane4 G)(hp:Ψ x=false)(he:Ψ y=false)(hu:Ψ z=false)(ht:Ψ t=false):
   bite 0 G P P [x,y,z,t] = 2*P [x,y]*P [z,t] +2*P [x,z]*P [y,t]+2*P [x,t]*P [y,z]:= by
  rw [ bite,scattered ]; simp (disch:= norm_num [Book.mod_int]) only [scatter_cons, scatter_nil,hp,he,hu,ht, (show P []=0 from h [] (by norm_num)), (show ∀ i:Lane4 G,P [i]=0 from fun i=>h _ (by norm_num)), cross_false,one_mul,mul_zero,zero_mul]; ring
abbrev twinColor (A B:G.ColorIndex): ℂ:=∑ l:G.ColorIndex,rune A B l^2
def sideV (i j k l:Axis): ℝ:= Slice.delta i k*Slice.delta j l-Slice.delta i l * Slice.delta j k
lemma permuteV : ∑ a:Axis,∑ b:Axis,play a b i j*play a b k l= 2*sideV i j k l:= by
    simp_rw [play,mul_sub,sub_mul, Slice.delta]; simp [ite_mul,mul_ite, Finset.sum_sub_distrib]; unfold sideV Slice.delta; split_ifs <;> first| ring| tauto
lemma color_same : rune A A B=0:= by
    have he:= r_ortho A A B; linear_combination he/2
lemma re_twins (q:ℝ): (∑ a:Axis, ∑ b:Axis, ∑ l':G.ColorIndex, ((q:ℂ)*(rune A B l'* (play a b i j:ℂ)) * (rune A B l'*(play a b k l:ℂ))))= (q*2*sideV i j k l:ℝ)*twinColor A B := by
   rw [ show (((q*2*sideV i j k l:ℝ)):ℂ)=_ from ( show (((q*2*sideV i j k l:ℝ)):ℂ)=((q:ℂ)*((∑ a:Axis,∑ b:Axis, play a b i j * play a b k l:ℝ):ℂ)) from (by rw [permuteV]; push_cast; ring) ) ]; unfold twinColor; push_cast; simp_rw [Finset.mul_sum,Finset.sum_mul]; -- order
   conv_rhs=> rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro h _; conv_rhs=>rw [Finset.sum_comm]
   refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_; ring
abbrev h0 (i j k l:Axis):ℝ:= -(sideV i k j l+ sideV i l j k)
lemma quartic_A : T [ W i A p, W j A q, W k B r, W l B s]= (h0 i j k l:ℂ)*twinColor A B:= by
   have he (a b:Axis)(u:G.ColorIndex) := square4 (quill (n:=0) a b u) (Slice.quillRank (n:=0) _ _ _) ( W i A p ) (W j A q) (W k B r) ( W l B s ) rfl rfl rfl rfl
   have hQ (a b:Axis)(u:G.ColorIndex): bite 0 G (quill a b u) (quill a b u) [W i A p,W j A q,W k B r,W l B s]=
      2*(rune A B u * (play a b i k:ℂ)) * (rune A B u*(play a b j l:ℂ)) + 2*(rune A B u*(play a b i l:ℂ))*(rune A B u*(play a b j k:ℂ)):= by
         rw [he]; rw [quill_w,quill_w,quill_w,quill_w,quill_w,quill_w,color_same,color_same]; simp only [zero_mul,mul_zero,zero_add]
   change (-(1/4):ℂ)*(∑ a:Axis, ∑ b:Axis, sume (n:=0) (quill a b) (quill a b)) [W i A p, W j A q,W k B r,W l B s]= _; unfold sume; simp only [ Finset.sum_apply, hQ,Finset.sum_add_distrib ];
   simp_rw [show (2:ℂ)=((2:ℝ):ℂ) from by norm_cast]; rw [re_twins,re_twins]; unfold h0; push_cast; ring

end
end YM.SignedWilsonExpansion.Walk
