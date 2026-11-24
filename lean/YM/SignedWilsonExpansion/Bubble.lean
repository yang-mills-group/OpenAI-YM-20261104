import YM.SignedWilsonExpansion.Replace
namespace YM.SignedWilsonExpansion.Bubble
/-! # One-loop high-sector shape calculation. Pure vector contribution.
Before projecting to angular components, resolve the momentum flow for each
of the two directions of a marked propagator, using shifted right momentum;
using energy as an *integrated* mark instead would give a different answer. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk
open scoped Classical Topology ContDiff BigOperators
open Energy (plane leg firstE)
variable {G:Gauge} {a b c d i j u v l m:Axis} {A B Cc T:G.ColorIndex}
  {h:ℝ→ℝ}{p q r k x y:FourP}
local notation "Ψ"=>field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
local notation "X" => Slice.rib
local notation "Y" => yMark a b
local notation "g" => Canvas.triple G
--local notation "f" => fun (S:FourP)=> lineL G h -- remove
local notation "be" => Bead.attach
lemma rib_rot : X a b c p q r=X b c a q r p:= by unfold Slice.rib; abel
lemma y_rot : yMark a b u i v p q r=yMark a b i v u q r p:= by unfold yMark; ring
lemma bond_neg (h:ℝ→ℝ) (p:FourP) : bond h (-p) a b=bond h p a b:= by rw [bond,bond, k_even,MS.Landau.sq_neg]

abbrev Ranked3 (H:Law G)(P:Axis→Axis→Axis→FourP→FourP→FourP→ℝ): Prop := ∀ (a b c:Axis) (p q r:FourP) (A B C:G.ColorIndex),
    H [W c C r, W a A p, W b B q] = Complex.I * rune C A B * (P a b c p q r:ℂ)
lemma tripleB : Ranked3 g X:= by intro a b c p q r A B C; rw [Slice.t_WWW,rib_rot]
lemma triangle : Ranked3 (firstE a b G 0) Y:= by intro _ _ _ _ _ _ _ _ _; rw [first_A, y_rot]

/- Uses density already cut by 1/2. -/
def feather (P:Axis→Axis→Axis→FourP→FourP→FourP→ℝ)(h:ℝ→ℝ)(u i v j:Axis)(k p r q:FourP):ℝ:=
    -(∑ l:Axis,∑ m:Axis,bond h (k+p) l m* X u i l k p (-(k+p)) * P v j m r q (k+p))
variable {H:Law G} {P:Axis→Axis→Axis→FourP→FourP→FourP→ℝ}
lemma lift (hp:Ranked3 H P) : be h g H [W u A k, W i B p] [W v A r,W j B q]= (feather P h u i v j k p r q:ℂ)*twinColor A B:= by
    rw [Area.contact g H h (-(k+p)) _ _ (by simp [net,W,qnote]), starLine]; simp only [neg_neg]
    let L:= [W u A k,W i B p]; let R:= [W v A r,W j B q]
    have hC b p: g ((C₀ b,p)::L)=0:= Area.at_CWW ..
    have hU i b p: g ((U₀ i b,p)::L)=0:= Area.at_UWW ..
    dsimp only [L] at hC hU; simp only [hC,hU,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero, Area.boolW_h,cross_false,one_mul]
    unfold twinColor; rw [ Finset.mul_sum ]; refine Finset.sum_congr rfl fun z _=>?_ ; unfold feather; simp_rw [bond_neg]; push_cast; simp_rw [ ← Finset.sum_neg_distrib, Finset.sum_mul ] -- direction?
    refine Finset.sum_congr rfl fun l _=> Finset.sum_congr rfl fun m _=>?_;
    rw [ show ( ( g [ (W₀ l z,-(k+p)), W u A k,W i B p ] ))= _ from tripleB u i l k p (-(k+p)) A B z, show (H [ (W₀ m z,k+p),W v A r,W j B q ])= _ from hp v j m r q (k+p) A B z, r_clock z A B ];
    linear_combination (norm:=(push_cast; ring)) ((h (k+p).sq*precision l m (k+p):ℝ):ℂ) * rune A B z^2 * (X u i l k p (-(k+p)):ℂ) * (P v j m r q (k+p):ℂ) * Complex.I_sq

lemma color_repeat (α β:Lane4 G)(hq:α.1.2=β.1.2)(w:Lane4 G): g [w,α,β]=0:=by
    rcases α with ⟨⟨f,z⟩,p⟩; rcases β with ⟨⟨u,y⟩,q⟩; rcases w with ⟨⟨v,x⟩,r⟩; change z=y at hq; subst y -- may not subst on proj.
    have he(x y:G.ColorIndex): rune x y y=0:= by rw [r_clock,color_same]
    have h(x y:G.ColorIndex): rune y x y=0:= by rw [r_ortho,he,neg_zero]
    rcases f with ⟨_|a,_|_⟩ <;> rcases u with ⟨_|i,_|_⟩ <;> rcases v with ⟨_|j,_|_⟩ <;> -- convert constructors into table objects. guess simp only via tables marked lhs explicit but no η; use `rw`, inst heavy across cases.
     skip
    · change g [(C₀ x,r),(C₀ z,p),(C₀ z,q)]=_; rw [at_CCC]
    · change g [(S₀ x,r),(C₀ z,p),(C₀ z,q)]=_; rw [at_SCC]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(W₀ j x,r),(C₀ z,p),(C₀ z,q)]=_; rw [at_WCC]
    · change g [(U₀ j x,r),(C₀ z,p),(C₀ z,q)]=_; rw [at_UCC]
    · change g [(C₀ x,r),(C₀ z,p),(S₀ z,q)]=_; rw [at_CCS]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(S₀ x,r),(C₀ z,p),(S₀ z,q)]=_; rw [at_SCS]
    · change g [(W₀ j x,r),(C₀ z,p),(S₀ z,q)]=_; rw [at_WCS]
    · change g [(U₀ j x,r),(C₀ z,p),(S₀ z,q)]=_; rw [at_UCS]
    · change g [(C₀ x,r),(C₀ z,p),(W₀ i z,q)]=_; rw [at_CCW]
    · change g [(S₀ x,r),(C₀ z,p),(W₀ i z,q)]=_; rw [at_SCW]
    · change g [(W₀ j x,r),(C₀ z,p),(W₀ i z,q)]=_; rw [at_WCW]
    · change g [(U₀ j x,r),(C₀ z,p),(W₀ i z,q)]=_; rw [at_UCW]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(C₀ x,r),(C₀ z,p),(U₀ i z,q)]=_; rw [at_CCU]
    · change g [(S₀ x,r),(C₀ z,p),(U₀ i z,q)]=_; rw [at_SCU]
    · change g [(W₀ j x,r),(C₀ z,p),(U₀ i z,q)]=_; rw [at_WCU]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(U₀ j x,r),(C₀ z,p),(U₀ i z,q)]=_; rw [at_UCU]
    · change g [(C₀ x,r),(S₀ z,p),(C₀ z,q)]=_; rw [at_CSC]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(S₀ x,r),(S₀ z,p),(C₀ z,q)]=_; rw [at_SSC]
    · change g [(W₀ j x,r),(S₀ z,p),(C₀ z,q)]=_; rw [at_WSC]
    · change g [(U₀ j x,r),(S₀ z,p),(C₀ z,q)]=_; rw [at_USC]
    · change g [(C₀ x,r),(S₀ z,p),(S₀ z,q)]=_; rw [at_CSS]
    · change g [(S₀ x,r),(S₀ z,p),(S₀ z,q)]=_; rw [at_SSS]
    · change g [(W₀ j x,r),(S₀ z,p),(S₀ z,q)]=_; rw [at_WSS]
    · change g [(U₀ j x,r),(S₀ z,p),(S₀ z,q)]=_; rw [at_USS]
    · change g [(C₀ x,r),(S₀ z,p),(W₀ i z,q)]=_; rw [at_CSW]
    · change g [(S₀ x,r),(S₀ z,p),(W₀ i z,q)]=_; rw [at_SSW]
    · change g [(W₀ j x,r),(S₀ z,p),(W₀ i z,q)]=_; rw [at_WSW]
    · change g [(U₀ j x,r),(S₀ z,p),(W₀ i z,q)]=_; rw [at_USW]
    · change g [(C₀ x,r),(S₀ z,p),(U₀ i z,q)]=_; rw [at_CSU]
    · change g [(S₀ x,r),(S₀ z,p),(U₀ i z,q)]=_; rw [at_SSU]
    · change g [(W₀ j x,r),(S₀ z,p),(U₀ i z,q)]=_; rw [at_WSU]
    · change g [(U₀ j x,r),(S₀ z,p),(U₀ i z,q)]=_; rw [at_USU]
    · change g [(C₀ x,r),(W₀ a z,p),(C₀ z,q)]=_; rw [at_CWC]
    · change g [(S₀ x,r),(W₀ a z,p),(C₀ z,q)]=_; rw [at_SWC]
    · change g [(W₀ j x,r),(W₀ a z,p),(C₀ z,q)]=_; rw [at_WWC]
    · change g [(U₀ j x,r),(W₀ a z,p),(C₀ z,q)]=_; rw [at_UWC]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(C₀ x,r),(W₀ a z,p),(S₀ z,q)]=_; rw [at_CWS]
    · change g [(S₀ x,r),(W₀ a z,p),(S₀ z,q)]=_; rw [at_SWS]
    · change g [(W₀ j x,r),(W₀ a z,p),(S₀ z,q)]=_; rw [at_WWS]
    · change g [(U₀ j x,r),(W₀ a z,p),(S₀ z,q)]=_; rw [at_UWS]
    · change g [(C₀ x,r),(W₀ a z,p),(W₀ i z,q)]=_; rw [at_CWW]
    · change g [(S₀ x,r),(W₀ a z,p),(W₀ i z,q)]=_; rw [at_SWW]
    · change g [(W₀ j x,r),(W₀ a z,p),(W₀ i z,q)]=_; rw [at_WWW]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(U₀ j x,r),(W₀ a z,p),(W₀ i z,q)]=_; rw [at_UWW]
    · change g [(C₀ x,r),(W₀ a z,p),(U₀ i z,q)]=_; rw [at_CWU]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(S₀ x,r),(W₀ a z,p),(U₀ i z,q)]=_; rw [at_SWU]
    · change g [(W₀ j x,r),(W₀ a z,p),(U₀ i z,q)]=_; rw [at_WWU]
    · change g [(U₀ j x,r),(W₀ a z,p),(U₀ i z,q)]=_; rw [at_UWU]
    · change g [(C₀ x,r),(U₀ a z,p),(C₀ z,q)]=_; rw [at_CUC]
    · change g [(S₀ x,r),(U₀ a z,p),(C₀ z,q)]=_; rw [at_SUC]
    · change g [(W₀ j x,r),(U₀ a z,p),(C₀ z,q)]=_; rw [at_WUC]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(U₀ j x,r),(U₀ a z,p),(C₀ z,q)]=_; rw [at_UUC]
    · change g [(C₀ x,r),(U₀ a z,p),(S₀ z,q)]=_; rw [at_CUS]
    · change g [(S₀ x,r),(U₀ a z,p),(S₀ z,q)]=_; rw [at_SUS]
    · change g [(W₀ j x,r),(U₀ a z,p),(S₀ z,q)]=_; rw [at_WUS]
    · change g [(U₀ j x,r),(U₀ a z,p),(S₀ z,q)]=_; rw [at_UUS]
    · change g [(C₀ x,r),(U₀ a z,p),(W₀ i z,q)]=_; rw [at_CUW]; first | rfl | simp only [color_same, he, h,neg_zero,mul_zero,zero_mul]
    · change g [(S₀ x,r),(U₀ a z,p),(W₀ i z,q)]=_; rw [at_SUW]
    · change g [(W₀ j x,r),(U₀ a z,p),(W₀ i z,q)]=_; rw [at_WUW]
    · change g [(U₀ j x,r),(U₀ a z,p),(W₀ i z,q)]=_; rw [at_UUW]
    · change g [(C₀ x,r),(U₀ a z,p),(U₀ i z,q)]=_; rw [at_CUU]
    · change g [(S₀ x,r),(U₀ a z,p),(U₀ i z,q)]=_; rw [at_SUU]
    · change g [(W₀ j x,r),(U₀ a z,p),(U₀ i z,q)]=_; rw [at_WUU]
    · change g [(U₀ j x,r),(U₀ a z,p),(U₀ i z,q)]=_; rw [at_UUU]


/- convenient finite split evaluation; two-output legs to left. -/
lemma scatter4 (α β x y:Lane4 G){f:Shared (Lane4 G) ℂ}(hv:∀ l r,l.length≠2→ f l r=0): scatter Ψ [α,β,x,y] f=
       f [α,β] [x,y]+ cross (Ψ β) (Ψ x) * f [α,x] [β,y]+cross (Ψ α) ((Ψ β) ^^ Ψ x)*f [β,x] [α,y]+
       cross (Ψ β) (Ψ y)*cross (Ψ x) (Ψ y)*f [α,y] [β,x]+ cross (Ψ α) ((Ψ β) ^^ Ψ y)*cross (Ψ x) (Ψ y)*f [β,y] [α,x]+cross ((Ψ α) ^^ Ψ β) ((Ψ x) ^^ Ψ y)* f [x,y] [α,β]:=by
    simp (disch:=simp) only [scatter_cons,scatter_nil, degree_cons,degree_nil,hv]; cases Ψ α <;> cases Ψ β <;> cases Ψ x <;> cases Ψ y <;> simp [cross] <;> abel
lemma spare (H:Law G) (l r:Legs (Lane4 G))(hv:l.length≠2): be h g H l r=0:= Bead.boundedL h H hv
lemma same_color (H:Law G)(x y:Lane4 G)(hz:x.1.2=y.1.2)(r:Legs (Lane4 G)): be h g H [x,y] r=0:= by unfold Bead.attach Bead.summit; simp_rw [color_repeat x y hz]; simp
def body (h:ℝ→ℝ)(u v i j:Axis)(k p r q:FourP): ℝ:= h0 u v i j+ 2*(feather X h u i v j k p r q + feather X h u j v i k q r p)
theorem cross_field (P:Shared (Lane4 G) ℂ) (hp:∀ l r,l.length≠2→ P l r=0)
   (Q:∀ x y:Lane4 G,x.1.2=y.1.2→∀ r,P [x,y] r=0) :
    let α:=W u A k; let β:=W v A r; let i':=W i B p; let j':=W j B q
    scatter Ψ [α,β,i',j'] P=P [α,i'] [β,j']+ P [β,i'] [α,j']+P [α,j'] [β,i']+P [β,j'] [α,i']:= by
       intro α β i' j'; rw [scatter4 _ _ _ _ hp,Q α β rfl,Q i' j' rfl]; simp [show Ψ α=false from rfl,show Ψ β=false from rfl, show Ψ i'=false from rfl,show Ψ j'=false from rfl]

lemma honorable (hc:k+r+p+q=0) : be h g g [W u A k,W i B p] [W v A r,W j B q] =
   be h g g [W v A r,W j B q] [W u A k,W i B p]:= by
    rw [ Bead.opposite h _ _ (show net [W u A k,W i B p]+net [W v A r,W j B q]=0 by simp only [W,qnote,net_cons]; change k+(p+0)+(r+(q+0))=0; rw [add_zero,add_zero,← hc]; abel) (Bead.prudeT G) (Bead.prudeT G) ]; exact one_mul ..
lemma cloud4 (hc:k+r+p+q=0) :
    ( B₂ G 0+Canvas.quad G h g g ) [W u A k,W v A r,W i B p,W j B q]= (body h u v i j k p r q:ℂ)*twinColor A B:= by
    rw [Pi.add_apply,quartic_A, Bead.A_quad, cross_field _ (spare g) (same_color g) ]
    rw [← honorable (A:=A) (B:=B) (u:=u) (v:=v) (i:=i) (j:=j) hc, ← honorable (A:=A) (B:=B) (u:=u) (v:=v) (i:=j) (j:=i) (show k+r+q+p=0 by rw [add_right_comm, hc])]; rw [ Bubble.lift tripleB, Bubble.lift tripleB ]; unfold body; push_cast; ring

def paint (h:ℝ→ℝ)(p:FourP)(a b i:Axis):ℝ:= h p.sq*p.sq*leg a b i p
local notation "P'" => fun p=>paint h p a b
lemma painted : strength a b h p i=4*P' p i:= by unfold strength paint; ring
lemma colorV (A B:G.ColorIndex): twinColor A B=twinColor B A:= by unfold twinColor; simp_rw [r_ortho B A,neg_sq]
lemma SumColor (h:G.Simple) : (∑ A:G.ColorIndex,twinColor A B)=(G.casimir:ℂ):= by simp_rw [colorV _ B]; exact Slice.r_sq B h
def center (h:ℝ→ℝ)(a b u i v j:Axis)(k p r q S:FourP):ℝ:=
    let p':=k+p
    let q':=k+p-S;
    -(∑ l:Axis,∑ m:Axis,(paint h p' a b l)*(paint h q' a b m)*X u i l k p (-p') * X v j m r q q')*4
lemma inner_field (S:FourP) :
    internal S a b h g g [W u A k,W i B p] [W v A r,W j B q]= (center h a b u i v j k p r q S:ℂ)*twinColor A B:= by
    let R:=k+p; have he: net [W u A k,W i B p]=R:= by simp [R,W,net,qnote]
    let J:= [W u A k, W i B p]; let L:=[W v A r,W j B q]
    have h' v x: pick S a b h ( Detect.C x R ) v g=0:= unused _ _ (by rintro ⟨i,h⟩; simp [Detect.C,qnote,ghost] at h) v g
    have hU v i x: pick S a b h (Detect.U i x R) v g=0:= unused _ _ (by rintro ⟨i,h⟩; simp [Detect.U,qnote] at h) _ _
    unfold internal; rw [he,starLine]; simp only [ show ∀ i x w,pick S a b h (U₀ i x,R) w g=0 from fun i x w=>hU w i x, show ∀ x w,pick S a b h (C₀ x,R) w g=0 from fun x w=>h' w x, mul_zero,Finset.sum_const_zero,add_zero,boolW_h,cross_false,one_mul,bond_neg ]; unfold twinColor; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _=>?_
    have take(m:Axis)(r'): pick S a b h ( W₀ m z,R ) r' g = ∑ α:Axis,(↑(4*paint h (R-S) a b α * leg a b m R):ℂ)* g (W α z (R-S)::r'):= by rw [show ( W₀ m z,R )=W m z R from rfl, picked ]; simp_rw [painted];
    unfold center; dsimp only; simp_rw [take, Finset.mul_sum]; push_cast; simp_rw [← Finset.sum_neg_distrib, Finset.sum_mul]; refine Finset.sum_congr rfl fun l _=>?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m _=>?_
    have hx: (∑ i:Axis,bond h R l i *leg a b i R)=paint h R a b l:= by rw [projection]; unfold paint; ring
    rw (occs:=.pos [1]) [show ↑(paint h (k+p) a b l)=(∑ i:Axis,(bond h R l i:ℂ)*(leg a b i R:ℂ)) from (by simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum,hx]; rfl) ]
    simp_rw [ Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_mul ]; apply Finset.sum_congr rfl; intro α _
    rw [ show g (( W₀ l z,-R)::[W u A k,W i B p])= _ from tripleB u i l k p (-R) A B z, show g [W m z (R-S),W v A r,W j B q]=_ from tripleB v j m r q _ A B z, r_clock z A B ];
    linear_combination (norm:=( unfold R bond; push_cast; ring )) ((bond h R l α:ℂ)* (X u i l k p (-R):ℂ)*(X v j m r q (R-S):ℂ)*4*(paint h (R-S) a b m:ℂ)*(leg a b α R:ℂ)*rune A B z^2 )* Complex.I_sq

/- Mixed ghost inputs at rank four. -/
section ghost
variable {x y α β:Lane4 G}{S:FourP}
def wing (x:Lane4 G):= Ψ x=true
lemma side (hx:wing x): ¬vector x:= fun he=> by obtain ⟨v,k,p,rfl⟩:= vector_ex x he; contradiction
lemma dot_in {l r:Legs (Lane4 G)}(he:∃ x∈r,wing x) : be h g (firstE a b G 0) l r=0:= by
    rcases he with ⟨x,hx,he⟩; have hz(i:Lane4 G): firstE a b G 0 (i::r)=0:= first_g _ ⟨x,List.mem_cons_of_mem _ hx,side he⟩; unfold Bead.attach Bead.summit; simp_rw [hz]; simp
lemma refl0 {l r:Legs (Lane4 G)}(he:degree Ψ l=true) : internal S a b h g g l r=0:= by
    unfold internal; rw [ starLine ]; have hm(x y): g ((W₀ x y,-net l)::l)=0:= by rw [← cub_eq]; refine BulkTop.cub_parity _ ?_; rw [degree_cons, he]; change true≠false; decide
    have nU z x: pick S a b h (U₀ z x,net l) r g=0:= unused _ _ (side (show wing (U z x (net l)) from rfl)) _ _
    have nC x: pick S a b h (C₀ x,net l) r g=0:= unused _ _ (side (show wing (C x (net l)) from rfl)) _ _
    simp only [ hm,nU,nC,mul_zero,zero_mul, add_zero, Finset.sum_const_zero ]
lemma spareI {l r:Legs (Lane4 G)}(hm:l.length≠2): internal S a b h g g l r=0:= by unfold internal; have he(i:Branch G Axis): g ((i,-net l)::l)=0:= Slice.trank _ (by simp; omega); simp [he]
lemma opposed (hq:x.1.2=y.1.2)(r:Legs (Lane4 G)) : internal S a b h g g [x,y] r=0:= by unfold internal; simp_rw [color_repeat x y hq]; simp

lemma ghost_I (hA:wing α)(hB:wing β)(hc:α.1.2=β.1.2) :
    principal S a b h g g [α,β,W i B p,W j B q]=0:= by
    have hp: Ψ α=true:=hA; have hx: Ψ β=true:=hB
    let x:= W i B p; let y:=W j B q; change scatter Ψ [α,β,x,y] (internal S _ _ _ _ _)=0
    rw [ scatter4 _ _ _ _ (fun _ _ ht=>spareI ht),opposed hc, opposed (x:=x) (y:=y) rfl ]; simp only [mul_zero,add_zero,zero_add]
    rw [refl0 (l:=[α,x]) (by rw [degree_cons,hp]; rfl),refl0 (l:=[α,y]) (by rw [degree_cons,hp]; rfl),refl0 (l:=[β,x]) (by rw [degree_cons,hx]; rfl),refl0 (l:=[β,y]) (by rw [degree_cons,hx]; rfl)]
    ring
lemma ghost_T (hA:wing α)(hB:wing β)(hc:α.1.2=β.1.2) :
    Flux.tree parity (lineL G h) g (firstE a b G 0) [α,β,W i B p,W j B q] =0:= by
    let x:= W i B p; let y:=W j B q; rw [ quad_tree, Bead.A_quad ]; change (2:ℂ)*scatter Ψ [α,β,x,y] _=0
    rw [ scatter4 _ _ _ _ (spare _), same_color _ _ _ hc,same_color _ x y rfl, dot_in (r:=[β,y]) ⟨β,by simp,hB⟩, dot_in (r:=[β,x]) ⟨β,by simp,hB⟩, dot_in (r:=[α,x]) ⟨α,by simp,hA⟩, dot_in (r:=[α,y]) ⟨α,by simp,hA⟩ ]; ring
end ghost

def leafPrice (h:ℝ→ℝ)(a b i j u v:Axis)(p q k S:FourP):ℝ:=
    2*(feather (yMark a b) h u i v j k p (-k) q + feather (yMark a b) h u j v i k q (-k) p) +
        (center h a b u i v j k p (-k) q S+center h a b u j v i k q (-k) p S)
lemma leaf_cost (S:FourP) :
    let w:= [W u A k,W v A (-k),W i B p,W j B q]
    Flux.tree parity (lineL G h) g (firstE a b G 0) w + principal S a b h g g w =
       ↑(leafPrice h a b i j u v p q k S + leafPrice h a b i j v u p q (-k) S)*twinColor A B:= by
    dsimp only
    rw [quad_tree, Bead.A_quad]; unfold Walk.principal Walk.op
    rw [cross_field _ (spare _) (same_color _), cross_field (internal S a b h g g) (fun _ _ hp=>spareI hp) (fun _ _ hv=>opposed hv) ]
    rw [ Bubble.lift triangle, Bubble.lift triangle, Bubble.lift triangle, Bubble.lift triangle,inner_field, inner_field,inner_field,inner_field ]; unfold leafPrice; rw [neg_neg]; push_cast; ring

/- assemble Cross terms of the trc. -/

end
end YM.SignedWilsonExpansion.Bubble
