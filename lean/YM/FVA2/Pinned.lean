import YM.FVA2.PoleUnit
/-!
# Pinning unit before resetting D.lead. Entire independently bound data from d=0.
-/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 6000
noncomputable section
namespace YM.FVA2.Frost
open Filter Topology Set Function MeasureTheory PertExtension
open Wilson Lattice MS MS.Menus MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Paint
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Book.Convolve MS.Koszul
open MS.Plane MS.High MS.High.Knobs MS.City MS.Arc MS.Tone MS.Tone.Frame MS.Rock MS.Rock.Path MS.Land
open MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.SpinCode ColorCode MS.Color MS.Plane.Wire MS.Plane.Flux
open Finset (mem_antidiagonal)
-- if name conflict Finset.antidiagonal hazard; use Nat
open MS.Logarithm Plate ArchTurn MS.Wind MS.Wind.Leading
open scoped Topology ContDiff Classical
variable {G:Gauge} (V:Warehouse G) (B:Booked (wings G)){m n:ℕ} (i: Owner G 0) (P:MS_Data G B)
local notation "B0"=> wings G
-- constant projection
lemma label_status : ColorCode.letterOn i= oneI i • Labels.unit G 0:= by
    let e:= Land.read i; let p:= letterOn i; let L:= Theater.orbit G; have hu:letterOn i ∈ Labels.Grade (0,0):= by
        rw [show ((0,0):ℕ×ℕ)=(e.size,e.grade) from Prod.ext rfl (tip0 e).symm]; exact Warehouse.label_grade (wings G) i.2
    obtain ⟨k,hk⟩:= Labels.scalar_grade 0 hu; have he:e.read=L (ColorCode.letterOn i).val:= Warehouse.scheme _ i.2; rw [hk] at he ⊢; obtain h0:k=oneI i:= by
       have ht:= congr_fun he []; rw [ Submodule.coe_smul,map_smul ] at ht; have hy: L (Labels.unit G 0).val= coin 1:= (show L (MvPolynomial.C (1:ℂ))= _ from Theater.cus (G:=G) _); -- defeq one? check
       rw [hy] at ht; exact Eq.symm (ht.trans (mul_one _))
    rw [h0]
lemma unit_φ (d:ℕ): V.marked d (V.scene d).e0= levels (0:ℤ) (Cylinder.piece (1:ℂ)):= by
    rw [Labels.Frame.e0,V.mark_own ]; unfold Warehouse.inkB Warehouse.grade; rw [ (V.scene d).zero_degree ]; obtain hX:V.artifact d 0=Cylinder.piece 1:= by
       apply (markEq ..).1; apply Eventually.of_forall; intro n; rw [show shown _ (piece (1:ℂ):Dot G Cover)= _ from coin_settled (post (wrap n)) (1:ℂ)]; obtain hp:= (V.poised d 0).pays n 0; rw [shift_nil ] at hp;
       let W:= Source.put ( Plate.bare (V.S d) 0 ) ( 0:Site n ); have he : W ∘ nation= fun _=>1 := funext fun x=> by unfold W; rw [Function.comp_apply, Plate.bare_put]; exact ( (congr_arg Complex.re ( congr_fun ( V.h d|>.unit ) (expandAt 0 (nation x)) )) ) -- arg expected real
       apply Subtype.ext; rw [hp.home,he, reads, ink_const, Complex.ofReal_one ]; rfl
    rw [hX]; rfl
lemma unit_mark : (V.native (wings G)).inkM 0 ( Land.read i ).grade i.2= oneI i • Book.levels 0 (Cylinder.piece (1:ℂ)):= by
   let p := ColorCode.letterOn i; rw [ V.describes ]; change V.insertW 0 (letterOn i)=_; rw [label_status i,map_smul]; unfold Warehouse.insertW; simp only [ LinearMap.comp_apply,LinearEquiv.coe_coe, Labels.Frame.coords_unit ]; congr 1; rw [ show ( V.scopeW 0 ).inverse _ _ = (V.scene 0).e0 from ?_, unit_φ V 0 ]; -- need W.inverse fixes e0
   let W:=V.scopeW 0; let q:= Warehouse.inftyQ G; let x: (V.scene 0).Coeff:= Pi.single 0 1; apply (W.conversion q).injective; change W.conversion q ((W.conversion q).symm x)= W.matrix q x; rw [LinearEquiv.apply_symm_apply ]; symm; unfold PertExtension.Heat.Frame.matrix; funext i; change (∑ t: V.Atom 0, x t • W.joint (Next.Rank.Normal.milk q (W.basis t))) i = x i; rw [Finset.sum_apply,Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)]; rw [ show x 0=1 from Pi.single_eq_same ..,one_smul,W.coefficientMatrix (show W.slots 0≤W.slots i by change ((V.scene 0).grades 0).2≤_; rw [ (V.scene 0).zero_degree ]; exact Nat.zero_le _) ]
   intro k _ hk; rw [show x k=0 from Pi.single_eq_of_ne hk _, zero_smul ]; rfl
lemma piece_off (n:ℕ) : Book.levels 0 (Cylinder.piece 1:Dot G Cover) n= if n=0 then Cylinder.piece 1 else 0:= by
   unfold levels; by_cases h:n=0; · subst n; rw [Nat.cast_zero, zero_add,if_pos rfl ]; apply Subtype.ext; funext l; let K:Dot G Cover:=Cylinder.piece 1; change mask 0 K.val l= K.val l; rcases l with _|⟨a,l⟩; exact enough (R:=ℂ) _ rfl; exact strange (F:=K.val) _ (by simp; omega)
   rw [ if_neg h,add_zero]; apply Subtype.ext; let K:Dot G Cover:=Cylinder.piece 1; funext l; change mask (n:ℤ) K.val l=0; by_cases ht:(l.length:ℤ)=(n:ℤ); · rw [ enough l ht ]; cases l; simp at ht; omega; rfl;
   exact strange _ ht
variable {i} -- binder only uses implicit? want explicit
lemma wobble_one (p:Team)(x:ℝ): wobble G p x (Book.levels 0 (Cylinder.piece (1:ℂ)))= Book.levels 0 (Cylinder.piece 1):= by
   let M:= Book.levels 0 (Cylinder.piece 1:Dot G Cover); let c:=shift p x; have he:substitute c M=M:= by
      funext n; by_cases hv:n=0; rw [hv,Program.pay0]; unfold M; rw [rules,piece_off, if_neg hv ]; refine Finset.sum_eq_zero fun i hi=>?_ ; rw [piece_off ]; split; swap; · exact smul_zero ..
      next h=> subst i; rw [Program.cut,pow_zero,PowerSeries.coeff_one ]; simp [hv] -- fragile
   ext1 n; by_cases hx:n=0; · rw [hx,whoZero];
   unfold wobble; rw [LinearMap.comp_apply,he,rolls,piece_off,if_neg hx ]; exact Finset.sum_eq_zero fun i hi=>by
       let Z: LightMode G Cover→Cn:= fieldV p x ∘ Prod.fst; unfold M; rw [piece_off ]; split; swap; · exact map_zero _
       next hv=> have hL:i.1≠0:= by obtain ht:= Finset.HasAntidiagonal.mem_antidiagonal.mp hi; omega
                 refine Subtype.ext (funext fun l=>?_); rw [train_v,offer]; cases l; simp [PowerSeries.coeff_one,hL]; exact mul_zero _
lemma pre_one (p:Team)(x:ℝ)(i:Owner G 0): Glyph.preambleM (V.native B0) p (Land.read i) x= oneI i • Book.levels 0 (Cylinder.piece (1:ℂ)):= by change wobble G p x (( V.native (wings G) ).inkM 0 (Land.read i).grade i.2)=_; rw [unit_mark V i,map_smul,wobble_one]
-- fix fees. give desired
variable (i)
def ℤunit (i:Owner G 0): Acts (wings G) 0:= fun n=> if n=0 then (script (Land.read i) 0).val else 0
lemma ℤinit (i:Owner G 0): FitOrder (Land.read i) (ℤunit i 0):= by rw [ℤunit, if_pos rfl]; exact (script (Land.read i) _).property rfl
lemma face_p (k:ℕ)(j: Glyph (wings G) 0) : (ℤunit i k).register j= if (j=Land.read i∧k=0) then 1 else 0:= by
   unfold ℤunit; split; · next h=> simp [script,h]
   next h=> rw [if_neg (fun v=> h v.2 )]; rfl
lemma sign_p (j:Glyph (wings G) 0)(k:ℕ)(x:ℝ) : Menus.oil (ℤunit i) j k x= if j= Land.read i∧k=0 then 1 else 0:= by unfold oil; rw [face_p ]; split <;> simp
lemma living (p:Team)(x:ℝ): scoreM ( V.native (wings G) ) p (ℤunit i) x= Glyph.preambleM ( V.native (wings G) ) p ( Land.read i ) x:= by
   unfold scoreM motto; rw [show prim (ℤunit i) x=0 from ?_,map_zero,map_zero,add_zero,add_zero ]; swap; · unfold prim; funext k; unfold ℤunit; split <;> rfl
   funext n; unfold rentM; simp_rw [sign_p,ite_smul,zero_smul,one_smul]; rw [ Finset.sum_eq_single_of_mem (Land.read i) (Finset.mem_univ _) ]; · rw [Finset.sum_eq_single (0,n)]; simp; intro j hj hn; have he:j.1≠0:= (by intro hv; obtain he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hj; exact hn (Prod.ext hv (by rw [hv,zero_add] at he; exact he))); simp [he]; simp
   intro j hj h; simp [h]
open MS.Heat
private abbrev K (i:Owner G 0)(n:ℕ): Wind.Flow G:= fun _=> coin (leer i n)
lemma pin_tree (F:Wind.Flow G)(n:ℕ) : treeP G F (K i n)=0:= by
   ext x l; change Plane.Flux.tree Landau.parity (Cpu G x) (F x) (coin (leer i n)) l= 0; refine Eq.trans ( scatter_congr _ l _ 0 (fun v u h=>?_)) (map_zero (allocate ..)); change Flux.attaches Landau.parity _ _ ( coin ( leer i n ) ) _ _= 0; unfold attaches; simp only [coin, mul_zero, add_zero, Finset.sum_const_zero ]
lemma pinT (X:Team): Tick X (G:=G) (fun n _=>K i n) (fun n x=>Tone.run (scoreM ( V.native (wings G) ) X ( ℤunit i ) x n)) := by
   have he (n:ℕ): TouchF (K i n):= by intro E _ _ f w _ h; cases w <;> exact contDiff_const
   have hm (n:ℕ): Rank (K i n) 0:= by intro x l hl; cases l; simp at hl; rfl
   refine ⟨ fun n p=> ?_, fun i _=>he i, fun n _=>⟨0,hm n ⟩⟩; rw [living, pre_one, Pi.smul_apply, piece_off ]; have hv:Wind.path 1 n 0 (skyline G X) ( fun n _=> K i n ) p=0:=by unfold Wind.path; simp only [one_smul, Finset.sum_apply,pin_tree, Finset.sum_const_zero ] -- pin_tree p not binder; remove.
   refine ⟨?_,fun t w=>?_⟩
   · unfold K leer; split; · rw [map_smul, show Tone.run _=coin (1:ℂ) from coin_turn .. ]; ext l; cases l; exact Eq.symm (mul_one _); exact Eq.symm (mul_zero _)
     rw [smul_zero,map_zero ]; ext l; cases l <;> rfl
   rw [ hv, Rank.gone (lapid_max (he _) (City.main_f _) (hm n)) (by omega) ]; simp only [Pi.zero_apply, add_zero]; exact hasDerivAt_const t (coin (leer i n) w)
open Blaze
lemma authentic (X:Team): col (horizonM (V.native B0) X (ℤunit i))=Archive 0 (P.marks 0 i):= by
   have he := Tick.unique (ticksM X _ _ _ (aquaM (V.native B0) X (ℤunit i))) (pinT V i X); rw [he]; ext n x l; obtain ⟨s,y⟩:= x; rw [archivE ]; rfl
variable (Q: Land.Prescription (wings G))
lemma pinKnow (H:TaylorOKM P ( V.native (wings G) ) Q) : Fixed (col (horizonM (V.native B0) Q.team (ℤunit i))) (Archive 0 (P.marks 0 i)) false 0 0:= by
   rw [authentic ]; intro k hk r hr E _ _ w hw hx; exact Like.same (fun i=> (Plane.at_start High.p_gain.le i).1.le) ((H.mark 0 i k hk r hr E w hw hx).std)
-- choose at zero only
-- Finite-h µ opts still.Pen
private def pins : ∀ d, Plaid (wings G) d→Acts (wings G) d | 0=> ℤunit | k+1=> Q.fees (k+1)
def recover : Land.Prescription (wings G) where
   team:= Q.team
   fees:= pins Q
   init d:= by cases d with |zero=> exact fun i=>ℤinit i| succ k=> exact Q.init (k+1)
lemma pinOK (h:TaylorOKM P (V.native B0) Q) : TaylorOKM P (V.native B0) (recover Q) := by
   exact ⟨ h.bulk,fun d=> by cases d with| zero=> exact fun i=> pinKnow V B i P Q h|succ k=>exact h.mark (k+1) ⟩ -- project n+1 defeq
structure Trusted (i:Land.Prescription (wings G)): Prop where
    unit (j: Owner G 0): i.fees 0 j= ℤunit j
lemma coinW (i:Owner G 0)(x:ℝ)(n:ℕ) : Blaze.sketch V (recover Q) 0 x n i = if n=0 then sameAxis V.F 0 (Land.read i) else 0 := by
    unfold Blaze.sketch Blaze.factory; change ∑ j: Glyph (wings G) 0, oil (ℤunit i) j n x • _= _; simp_rw [sign_p,ite_smul,one_smul,zero_smul ]; by_cases h:n=0 <;> simp [h]
lemma pinLegal (h: ExactSpin V Q) : ExactSpin V (recover Q) := by
   constructor; intro s d i x n; cases d
   · change spin V.F s.ortho 0 ( Blaze.sketch V (recover Q) 0 x n i )= ∑ k: Owner G 0,ColorCode.fee _ _ _ i k • Blaze.sketch V (recover Q) 0 x n k; simp_rw [ coinW V Q ]; by_cases he:n=0; · simp only [he,if_true]; rw [ owners ]; simp_rw [show ∀ (i:ℝ)(p:Pert.Position.E V.F 0),(i:ℂ) • p=i • p from fun i p=> IsScalarTower.algebraMap_smul ℂ i p]; -- equality
     simp [he]
   exact h.legal ..
lemma proficient (h:TaylorOKM P ( V.native (wings G) ) Q)(hp: Turns V P): ∃ X : Prescription (wings G), TaylorOKM P (V.native (wings G)) X ∧ ExactSpin V X ∧ Trusted X ∧ X.team = Q.team:= ⟨ recover (vision V Q),pinOK V B P _ ( together V P Q hp h ),pinLegal V _ (vision_angular V Q),⟨ fun _=> rfl⟩,rfl⟩
end YM.FVA2.Frost
