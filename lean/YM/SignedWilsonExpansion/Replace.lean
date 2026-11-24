import YM.SignedWilsonExpansion.Atom
namespace YM.SignedWilsonExpansion.Walk
/-! A marked *quadratic* insertion propagated on trees.

When root momentum is S a hop on one chosen gauge leg is from p to (p-S).
Implemented before summing or twisting ANY phase. Internal propagator
responses must use the same shift. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area
open HighScale HighRank TreeLine TreeView
open Energy (plane firstE leg)
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {a b:Axis} {h:ℝ→ℝ} {t:ℝ}
local notation "Ψ"=>field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
abbrev travel (S:FourP)(α:Axis)(i:Lane4 G) : Lane4 G:= ((if vector i then gauge α else i.1.1,i.1.2), i.2-S)
def strength (a b:Axis)(h:ℝ→ℝ)(p:FourP)(c:Axis): ℝ:= 4*p.sq*h p.sq *leg a b c p
def wish (a b:Axis)(h:ℝ→ℝ)(S:FourP)(α:Axis) : Lane4 G→ℂ
  | (((some i,false),j),p)=> ↑(strength a b h (p-S) α* leg a b i p)
  | _=>0
local notation "Rₛ" => wish a b h
lemma travel_par (S:FourP)(α:Axis)(i:Lane4 G): Ψ (travel S α i)= Ψ i:= by
    by_cases he: vector i; · obtain ⟨i,k,p,rfl⟩:= vector_ex i he; unfold travel; rw [if_pos he]; rfl
    unfold travel; rw [if_neg he]
lemma travel_W (S:FourP)(α:Axis)(i:Axis)(k:G.ColorIndex)(p:FourP) :
    travel S α (W i k p)= W α k (p-S):= by unfold travel; rw [ if_pos (vector_A ..) ]
lemma wish_W (S:FourP)(α:Axis)(i:Axis)(k:G.ColorIndex)(p:FourP) :
    Rₛ S α (W i k p)= ↑(strength a b h (p-S) α* leg a b i p):= rfl
lemma wish_other (S:FourP)(α:Axis)(i:Lane4 G)(hp:¬vector i): Rₛ S α i=0:= by
    rcases i with ⟨⟨⟨_|i,_|_⟩,k⟩,p⟩ <;> first | rfl| exact (hp (vector_A ..)).elim

section runner
variable {A I:Type}{p:Sector A}
-- single direction combinator
def hop (R:A→ℂ)(v:A→A): Legs A → Raw A ℂ →ₗ[ℂ] ℂ
  | []=>0
  | i::l=> R i • LinearMap.proj ( v i::l ) + (hop R v l) ∘ₗ D i
variable {R':A→ℂ}{v:A→A}
local notation "U" => hop R' v
lemma step (R:A→ℂ)(v:A→A)(i:A)(l:Legs A)(F:Raw A ℂ): hop R v (i::l) F= R i * F (v i::l)+hop R v l ( D i F ):= rfl
lemma step0 (F:Raw A ℂ): U [] F=0:= rfl
lemma hop_sign (b:Bool)(hp:∀ i, p (v i)=p i)(l:Legs A)(F:Raw A ℂ): U l (sign p b F)=cross b (degree p l)*U l F:=by
    induction l generalizing F with
    | nil=>rw [step0,step0,mul_zero]
    | cons i l ih=> rw [step,step, sign_D,map_smul, ih,at_sign,degree_cons,degree_cons,hp,cross_right]; change _+ ((cross b (p i):ℂ)*_) = _; ring
def op (p:Sector A) (u:Shared A ℂ) : Raw A ℂ := fun w=> scatter p w u
lemma hop_scatter (u:Shared A ℂ)(hp:∀ i,p (v i)=p i)(w:Legs A): U w (op p u) = scatter p w (fun l r=> U l (fun x=>u x r)+ U r (fun y=>u l y)):= by
   induction w generalizing u with
   | nil =>rw [scatter_nil,step0,step0,step0,add_zero]
   | cons i w ih=>
     let c:=cross (R:=ℂ) (p i)
     let h(i:A)(l r:Legs A):= u (i::l) r + c (degree p l)*u l (i::r)
     have he : D i (op p u)=op p (h i):= rfl
     let H:= allocate p w (R:=ℂ); let y:= fun l r=> U l (fun x=>h i x r)+U r (fun y=>h i l y)
     have hx: op p u (v i::w)=H (h (v i)):= by unfold op; rw [scatter_cons,hp]; rfl
     rw [step,he,hx, ih, scatter_cons]; change R' i • H _ + H y=_
     rw [← map_smul, ← map_add]; apply scatter_congr; intro l r ht; simp only [Pi.add_apply, Pi.smul_apply, y, step]
     have e₁: (fun x=> h i x r)=(fun x=>u (i::x) r)+sign p (p i) (fun x=>u x (i::r)):=rfl
     have e₂: (fun y=>h i l y)=(fun y=>u (i::l) y)+c (degree p l) • D i (u l):= rfl
     rw [e₁,e₂,map_add,map_add, hop_sign _ hp, map_smul]
     simp only [h,c,smul_eq_mul]; change _= R' i* _ + hop R' v l (fun x=> u (i::x) r) + hop R' v r (u (i::l))+ _ * (_+ (R' i * u l _ + hop R' v r (D i (u l)))); ring
end runner

def changeS (S:FourP)(a b:Axis)(h:ℝ→ℝ)(u:Law G) : Law G:= fun w=>∑ i:Axis, hop (wish a b h S i) (travel S i) w u
local notation "Uρ" => fun (S:FourP) (u:Law G)=> changeS S a b h u
def changeF (S:FourP)(a b:Axis)(h:ℝ→ℝ): Op (Lane4 G) ℂ where
    toFun := changeS S a b h
    map_add' u v:= by funext w; simp only [changeS,map_add,Finset.sum_add_distrib]; rfl
    map_smul' c u:=by funext w; simp only [changeS,map_smul, Finset.smul_sum, Pi.smul_apply]; rfl
local notation "𝓥" => fun S':FourP=> changeF (G:=G) S' a b h
def pick (S:FourP)(a b:Axis)(h:ℝ→ℝ)(i:Lane4 G)(l:Legs (Lane4 G))(F:Law G):ℂ:= ∑ α:Axis, wish a b h S α i*F (travel S α i::l)
local notation "Φ" => fun S':FourP=> pick (G:=G) S' a b h
lemma chosen (S:FourP)(i:Lane4 G)(l:Legs (Lane4 G))(F:Law G): 𝓥 S F (i::l)=(Φ S) i l F+𝓥 S ( D i F ) l:= by
    change (Uρ S F) _=_ + Uρ S ( D i F ) l; unfold changeS; simp_rw [step, Finset.sum_add_distrib]; rfl
lemma c_empty (S:FourP)(F:Law G):𝓥 S F []=0:=by change changeS S _ _ _ F []=_; unfold changeS; simp only [step0,Finset.sum_const_zero]
lemma unused (S:FourP)(i:Lane4 G)(hp:¬vector i)(l:Legs (Lane4 G))(F:Law G): pick S a b h i l F=0:=by unfold pick; simp [wish_other S _ i hp]
lemma picked (S:FourP)(i:Axis)(k:G.ColorIndex)(p:FourP)(l:Legs (Lane4 G))(F:Law G): pick S a b h (W i k p) l F=∑ α:Axis,(↑(strength a b h (p-S) α* leg a b i p):ℂ)* F (W α k (p-S)::l):= by unfold pick; simp_rw [wish_W,travel_W]
lemma signF (S:FourP)(z:Bool)(F:Law G)(w:Legs (Lane4 G)) : (𝓥 S) (sign Ψ z F) w= cross z (degree Ψ w)*(𝓥 S) F w:= by
    change Uρ S _ w=_* Uρ S _ w; unfold changeS; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> hop_sign z (travel_par S i) w F
lemma shifts_S (S:FourP) {F H:Law G}(w:Legs (Lane4 G))(eq:∀ w',net w'=net w-S→F w'=H w'): (𝓥 S) F w=(𝓥 S) H w:= by
    induction w generalizing F H with
    | nil=>rw [c_empty,c_empty]
    | cons i w ih=>
       have he α: net (travel S α i::w)= net (i::w)-S:=by rw [net_cons,net_cons]; change i.2 - S + _ =_; abel
       simp only [chosen,pick,eq _ (he _)]; congr 1; apply ih; intro w' hx; apply eq (_::w'); rw [net_cons,net_cons,hx]; abel
lemma program (S:FourP)(w:Legs (Lane4 G))(F:Shared (Lane4 G) ℂ): 𝓥 S (op Ψ F) w= allocate Ψ w (fun l r=> 𝓥 S (fun x=>F x r) l+𝓥 S (F l) r):= by
    change (∑ α:Axis,hop (wish a b h S α) (travel S α) w _)=allocate Ψ w (fun l r=> Uρ S (fun x=>F x r) l + Uρ S (F l) r)
    simp_rw [hop_scatter F (travel_par S _)]; unfold changeS; let H:= allocate Ψ w (R:=ℂ)
    let f (i:Axis)(l r:Legs (Lane4 G)):= hop (wish a b h S i) (travel S i) l (fun x=>F x r)+hop (wish a b h S i) (travel S i) r (F l)
    refine Eq.trans (Eq.symm ( map_sum H f _ )) ?_; apply scatter_congr; intro l r _; simp only [ Finset.sum_apply,f, Finset.sum_add_distrib]

local notation "N" => plane a b G 0
variable (S:FourP)

lemma used (F:Law G)(l:Legs (Lane4 G))(i:Axis)(k:G.ColorIndex)(p:FourP)(hv:S=net l+p) : R G h F N l [W i k p] = pick S a b h (W i k p) l F:= by
    rw [chart, Area.contact _ _ h (-net l) _ _ rfl, starLine ]; simp only [neg_neg]
    let g (j:Branch G Axis):= j
    have he (t:Axis)(j:G.ColorIndex): N [(U₀ t j,net l), W i k p]=0:= plane_g _ ⟨_,List.mem_cons_self, show ¬vector ( U t j (net l) ) from by rintro ⟨t,h⟩; simp [U,qnote,vector] at h⟩ -- h does not contain vector
    have hx (j:G.ColorIndex): N [(C₀ j,net l), W i k p]=0:= plane_g _ ⟨_,List.mem_cons_self, show ¬vector ( C j (net l) ) from by rintro ⟨t,h⟩; simp [C,qnote,ghost] at h⟩
    have hz (t:Axis)(j:G.ColorIndex): N [(W₀ t j, net l), W i k p]=(if j=k then ↑((-2:ℝ)*leg a b t (net l)* leg a b i p:ℝ) else (0:ℂ)):= peel
    simp only [he,hx,mul_zero,zero_mul, Finset.sum_const_zero, add_zero]; rw [picked]
    simp only [ hz, Area.boolW_h, cross_false, one_mul ]; rw [ Finset.sum_eq_single k ]
    · have hc : p-S= -net l:= by rw [hv]; abel
      simp only [ hc, ↓reduceIte, Finset.mul_sum ]; refine Finset.sum_congr rfl fun j _=>?_ ; unfold strength; rw [show (4:ℝ)*Momentum.sq (-net l)*h _ *leg a b j (-net l)=4*(∑ α,bond h (-net l) j α*leg a b α (-net l) ) from (by rw [projection]; ring) ]
      push_cast; simp_rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro α _; rw [leg_neg]; push_cast; change (2:ℂ)*(_*(F (W j k (-net l)::l)*_))= _; ring
    · intro b _ hb; simp [hb]
    simp
def bill (S:FourP)(a b:Axis)(h:ℝ→ℝ)(F:Law G) (l r:Legs (Lane4 G)):= match r with
    | [i]=> pick S a b h i l F
    | _=>0
omit S
lemma rejected (F:Law G)(l r:Legs (Lane4 G))(hv:r.length≠1) : R G h F N l r=0:= by
    have he(i:Lane4 G): N (i::r)=0:= ranked_N _ (by rw [mod_int]; simp; omega)
    simp [R,attaches,he]
include S
lemma in_mark (F:Law G)(l r:Legs (Lane4 G))(hn:S=net l+net r): R G h F N l r=bill S a b h F l r:= by
    by_cases hv:r.length=1
    · obtain ⟨i,rfl⟩:= List.length_eq_one_iff.mp hv; change _=pick S a b h i _ F
      by_cases hx: vector i
      · obtain ⟨i,k,p,rfl⟩:= vector_ex i hx; apply used S F l i k p; convert hn using 2; simp [net,W,qnote]
      have hu (j:Lane4 G): N [j,i]=0:= plane_g _ ⟨i,(by simp),hx⟩
      rw [unused S i hx]; simp only [R,attaches,hu,mul_zero,add_zero, Finset.sum_const_zero]
    rw [ rejected _ _ _ hv ]; rcases r with _|⟨i,_|s⟩; exacts [rfl,(hv rfl).elim,rfl]
lemma pay (F:Law G)(hp:Symm Ψ F)(l:Legs (Lane4 G)):
    scatter Ψ l (bill S a b h F) = 𝓥 S F l:= by
    induction l generalizing F with
    | nil=>rw [scatter_nil,c_empty]; rfl
    | cons i l ih=>
       rw [scatter_cons,chosen, ← ih ( D i F ) (hp.drop _)]
       let A:=bill (G:=G) S a b h; let F'(x y:Legs (Lane4 G)):= A F (i::x) y + cross (Ψ i) (degree Ψ x)* A F x (i::y); let μ:= allocate Ψ l (R:=ℂ)
       let Y(x y: Legs (Lane4 G)):= if y.length=0 then pick S a b h i x F else 0
       have hM: μ Y= pick S a b h i l F:= by
          change scatter Ψ l Y=_; rw [ MS.Motif.swap ]; refine Eq.trans (scatter_congr _ _ _ (fun x y=> if x.length=0 then pick S a b h i y F else 0) (fun a b' _=>?_)) ( MS.Plane.onlyEmpty .. ); cases a with| nil=>simp [Y]| cons i a=>simp [Y]
       change μ F' = pick _ _ _ _ _ l _ + μ _
       rw [← hM, ← map_add]; apply scatter_congr; intro x y _
       change F' x y=Y x y + A ( D i F ) x y
       rcases y with _|⟨j,_|r⟩
       · -- if i gauge pay sign =1
         by_cases he: vector i
         · have ht: Ψ i=false:= by obtain ⟨i,k,p,rfl⟩:= vector_ex i he; rfl
           unfold F' Y A bill; simp [ht]
         simp [F',Y,A,bill,unused S i he]
       · by_cases he: vector j
         swap; · simp [F',Y,A,bill,unused S j he]
         unfold F' Y A; simp only [bill,List.length_cons,List.length_nil,Nat.succ_ne_zero,one_ne_zero,↓reduceIte,zero_add,mul_zero,add_zero]
         obtain ⟨j,k,p,rfl⟩:= vector_ex j he; unfold pick; refine Finset.sum_congr rfl fun α _=> ?_;
         rw [at_D]; let v:=travel S α (W j k p); have hx: F (v::i::x)=F (i::v::x):= (hp [] v i x).trans (by rw [show Ψ v=false from (travel_par ..).trans rfl,cross_false]; exact one_mul _)
         rw [show F (_::i::x)= _ from hx]
       unfold F' Y; simp [A,bill]
lemma replacement (F:Law G)(hp:Symm Ψ F)(l:Legs (Lane4 G))(hn:S=net l):
    Flux.tree parity (lineL G h) F N l = 𝓥 S F l:=
  Eq.trans (scatter_congr Ψ l (R G h F N) _ (fun i j hi=> in_mark S F i j (hn.trans (split_net hi).symm))) (pay S F hp l)

local notation "Hb" => ((2:ℂ)⁻¹)
section debt
-- shift a leg counted on the ket side only. Crystal: includes both directions along same Hermitian summand by reversal.
def due (S:FourP)(a b:Axis)(h:ℝ→ℝ)(F H:Law G) : Shared (Lane4 G) ℂ:= fun l=> changeF S a b h (Bead.attach h F H l)
def internal (S:FourP)(a b:Axis)(h:ℝ→ℝ)(F H:Law G) : Shared (Lane4 G) ℂ:= fun l r=>
    ∑ (i:Branch G Axis),∑ j,lineL G h i j (-net l) * (cross (parity j) (degree Ψ l)*F ((i,-net l)::l)*pick S a b h (j,net l) r H)
lemma chargeR (F:Law G)(l:Legs (Lane4 G))(hp:Bead.Prude F)(hn:S=net l): 𝓥 S (Canvas.quad G h F F) l=2*allocate Ψ l (due S a b h F F):= by
    let P:Shared (Lane4 G) ℂ:= Bead.attach h F F
    let X₁:Shared (Lane4 G) ℂ := fun l r=> 𝓥 S (fun x=> P x r) l
    rw [ funext (fun w=> Bead.A_quad h F F w) ]; change (𝓥 S) (op Ψ P) l=_; rw [program]
    let A:= allocate Ψ l (R:=ℂ)
    let Q:=due S a b h F F
    have he(l r:Legs (Lane4 G))(ht:S=net l+net r): Q l r=cross (degree Ψ l) (degree Ψ r)* X₁ r l:= by
       unfold Q X₁ due; rw [← signF S (degree Ψ l) (fun x=>P x l) r]; apply shifts_S S
       intro u hv; have hn: net l+net u=0:= by rw [hv,ht]; abel
       exact Bead.opposite h _ _ hn hp hp
    change A (X₁+Q)=2*A Q
    have hv: A X₁=A Q:=by change scatter _ l _= _; rw [ Motif.swap ]; refine scatter_congr Ψ l _ Q ?_; intro i j hx; exact (he i j (hn.trans (split_net hx).symm)).symm
    rw [map_add,hv,two_mul]
lemma debit (F H:Law G)(l r:Legs (Lane4 G)) :
    Bead.attach h F (𝓥 S H) l r=internal S a b h F H l r + due S a b h F H l r:= by
    let v:Legs (Lane4 G)→ℂ:= Bead.attach h F H l
    let X (i j:Branch G Axis):ℂ:= lineL G h i j (-net l)*(cross (parity j) (degree Ψ l)*F ((i,-net l)::l))
    let w (i j:Branch G Axis):Law G:= X i j • D (j,net l) H
    have he: v=∑ i,∑ j,w i j:= by funext z; simp only [v,w,Finset.sum_apply,Bead.attach, X,Bead.summit,Pi.smul_apply,smul_eq_mul,at_D,neg_neg]
    unfold internal; unfold Bead.attach Bead.summit; change _= _+(𝓥 S) v r
    simp_rw [neg_neg,chosen,he,map_sum,Finset.sum_apply,w,map_smul,Pi.smul_apply,← Finset.sum_add_distrib] -- order/map_smul
    apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=>?_ ; dsimp only [X]; simp only [smul_eq_mul, mul_assoc,Canvas.line4,lineL]; ring
lemma tally (F:Law G)(l:Legs (Lane4 G))(hP:Symm Ψ F)(hn:S=net l): Canvas.quad G h F (Flux.tree parity (lineL G h) F N) l = allocate Ψ l (internal S a b h F F)+allocate Ψ l (due S a b h F F):= by
    rw [←map_add, Bead.A_quad]; apply scatter_congr; intro x y he; rw [Pi.add_apply, Pi.add_apply, ← debit]
    unfold Bead.attach Bead.summit; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; dsimp only; rw [replacement S F hP _ (by rw [hn,neg_neg,net_cons, ← split_net he])]

abbrev principal (S:FourP)(a b:Axis)(h:ℝ→ℝ)(F H:Law G) : Law G:= op Ψ (internal S a b h F H) -- notation Ψ captures G?
lemma decision (F:Law G)(w:Legs (Lane4 G))(hn:S=net w):
    MarkTop.charged (Energy.called a b G) F t w = Flux.tree parity (lineL G (amp t)) (Canvas.triple G) F w +
      changeF S a b (amp t) ( B₂ G 0+ Canvas.quad G (amp t) (Canvas.triple G) (Canvas.triple G) ) w + principal S a b (amp t) (Canvas.triple G) (Canvas.triple G) w:= by
    let U:= Canvas.triple G; let P:= Canvas.quad G (amp t) U U
    have hp:Symm Ψ U:=(fund_one G 0).sym
    have hf:Symm Ψ P:= (tree_sym (Shells.closure G _) hp hp).smul _
    have he:= replacement (a:=a) (b:=b) (h:=amp t) S (B₂ G 0) ( B₂_P G 0|>.sym ) w hn
    have hv:= tally (a:=a) (b:=b) (h:=amp t) S U w hp hn; have hV:= chargeR (a:=a) (b:=b) (h:=amp t) S U w (Bead.prudeT G) hn
    let X:=changeF (G:=G) S a b (amp t)
    unfold MarkTop.charged MarkTop.lump MarkTop.folded MarkTop.part
    rw [Energy.found, ampL, show BulkTop.cloud G t=P from (by unfold BulkTop.cloud; rw [ampL,cub_eq]; rfl), cub_eq]; simp only [ map_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add ]
    have hm:= replacement (a:=a) (b:=b) (h:=amp t) S P hf w hn
    change Flux.tree parity _ ( B₂ G 0 ) N w + _ + ( _ + Canvas.quad G (amp t) U _ w ) = Flux.tree _ _ _ _ _ + (X _ w+X P w) + allocate Ψ w (internal S a b (amp t) U U)
    rw [hv,he,hm, show X P w=_ from hV]; beta_reduce; dsimp only [X]; ring
end debt
end
end YM.SignedWilsonExpansion.Walk
