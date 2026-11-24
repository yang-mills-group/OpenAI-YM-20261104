import YM.FVAAlt2.Plus.Menu
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land

/-! RichBook generalization. Adapted from `MS/Menus/Tape`, `MS/Menus/Mark`, `MS/Menus/Quantify`, `MS/Wind/Clone`, `MS/Wind/Portfolio`, `MS/Wind/Lead`, `MS/Wind/MatchM`, `MS/Mach/Land`. -/

set_option autoImplicit false
noncomputable section

-- Menus/Tape
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G} (V : RichBook B)(p:Team) {d:ℕ}
variable (A:Acts B d)
def rentPl (x:ℝ) (i:ℕ): Dot G Cover:= ∑ g:Glyph B d, ∑ d∈antidiagonal i, oil A g d.1 x • Glyph.preamblePl V p g x d.2
def scorePl (x:ℝ): T (Dot G Cover):= rentPl V p A x + motto p A x
lemma markSensePl (x:ℝ) : scorePl V p A x= rentPl V p A x+ steadyE (Spectrum G) (style G p x) (prim A x):= rfl
lemma steadyPl (k:ℕ) (P:Acts B d) (H:∀ i, i≤ k→ A i=P i) (x:ℝ): scorePl V p A x k=scorePl V p P x k := by
    simp_rw [scorePl,Pi.add_apply,sky,rentPl, H k k.le_refl]
    apply congr_arg₂ (·+·)
    · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj; unfold oil; rw [H j.1 (by obtain h:=mem_antidiagonal.mp hj; omega)]
    congr 1; apply Finset.sum_congr rfl; intro j hj; rw [H j.2 (by obtain h:=mem_antidiagonal.mp hj; omega)]
lemma posesPl (x:ℝ)(i:ℕ): Tuned (rentPl V p A x i) 0:= Tune.sum _ fun g _=> Tune.sum _ fun j _=> (Glyph.pre_cPl V p g x j.2).cash _ (show star (oil A g j.1 x)=_ from by simp [oil])
lemma appearsPl (x:ℝ)(i:ℕ): Colorless (rentPl V p A x i):= Colorless.csum _ fun g _=> Colorless.csum _ fun j _=> (Glyph.pre_litPl V p g x j.2).smul _
lemma rentReadyPl (i:ℕ): Ready (fun x=> rentPl V p A x i):= value_sum _ (fun j _=> value_sum _ (fun k _=> pc_ready (c:=oil A j k.1) ⟨_,Ready.got _,rfl⟩ (Glyph.pre_readyPl V p j k.2)))
lemma rentLimitPl (x:ℝ)(i:ℕ): Limit (rentPl V p A x i).val (i+d):= by unfold rentPl; simp_rw [sum_stack]; exact Limit.sum _ (fun g _=> Limit.sum _ (fun k hk=> ((Glyph.pre_costPl V p g x k.2).smul _).up (by obtain he:= Finset.mem_antidiagonal.mp hk; have hv:= Glyph.memory g; omega)))
lemma rangePl (x:ℝ)(i:ℕ): Limit (scorePl V p A x i).val (i+d+fringe A i):= Limit.add ((rentLimitPl V p A x i).up (by omega)) ((stuff p A x i).up (by omega))
lemma decorPl : Circle G (scorePl V p A) false 0 where
    stance0 _ _ h:= False.elim (Bool.noConfusion h)
    actual i x:= (posesPl V p A x i).add (pretty p A x i)
    settled i x:=(appearsPl V p A x i).add (colorRoot p A x i)
    tag i:= (rentReadyPl V p A i).add (flows p A i)
    room i:=⟨i+d+fringe A i,fun x=>by exact_mod_cast (rangePl V p A x i)⟩
end YM.MS.Menus

-- Menus/Mark
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : RichBook B)(p:Team) {d n:ℕ} (x:ℝ)
section close
variable (A:Acts B d)(H:G.Simple)
include H
lemma rentedPl : Weightless (Spectrum G) (style G p x) (rentPl V p A x):= by
    let P:=Spectrum G; let T:Glyph B d→ T (Dot G Cover):= fun i=> Glyph.preamblePl V p i x;
    let U (ζ:Glyph B d)(n:ℕ) := oil A ζ n x; let X := style G p x; let D:=actB (Spectrum G)+ pairW (Spectrum G).touch X; let J:= pairW (LinearMap.lsmul ℂ (Dot G Cover));
    have he c f: actB P (J c f)=J c (actB P f):= by funext n; unfold actB J; simp only [paired,promised, LinearMap.lsmul_apply,map_sum,map_smul]
    have hd (i:Glyph B d): D (J (U i) (T i)) =0:= by rw [show D (J (U i) (T i))=J (U i) (D (T i)) from ?_,show D (T i)=0 from Glyph.pre_freePl V p i x H,map_zero]; unfold D; simp only [LinearMap.add_apply, olio, J,map_add]; rw [show actB (Spectrum G) _ =_ from he (U i) (T i)] -- lint
    change D _=0; rw [show rentPl V p A x=∑ g:Glyph B d,J (U g) (T g) from funext fun n=> by unfold rentPl; simp only [Finset.sum_apply]; rfl,map_sum]; simp_rw [hd,Finset.sum_const_zero]
lemma lawPl : Weightless (Spectrum G) (style G p x) (scorePl V p A x):= by
    let Q := actB (Spectrum G)+ blocks (Spectrum G) (style G p x); change Q (rentPl V p A x+motto p A x)=0
    have hh : Q (motto p A x)=0 := steady_squares (style G p x) _ (main_law G p x H) (fun i=> ((core_circle G p).actual i x).symm) (fun i=> Tune.parity ((core_circle G p).actual i x) ghostParity) (fun i=> ((A i).proof.actual x).symm)
    rw [map_add,hh,show Q (rentPl V p A x)=0 from rentedPl V p x A H,zero_add]
end close
def lightingPl (Q: Price B d) (x:ℝ): Dot G Cover:= ∑ c:Glyph B d, (↑((Q c).eval x):ℂ) • Glyph.preamblePl V p c x 0
variable (A:Acts B d)(Q:Price B d)(X:Power G)
lemma repairPl : scorePl V p A x n-scorePl V p (patch A Q X n) x n= lightingPl V p Q x + advance (X.input x):= by
   let S:= patch A Q X n; have hc : (A n).proof.input x-(S n).proof.input x = X.input x:= by simp [S,patch,Power.sub] -- may `sub_sub`
   have hs (i:Glyph B d) : ∑ j∈antidiagonal n,(oil A i j.1 x - oil S i j.1 x) • Glyph.preamblePl V p i x j.2= (↑((Q i).eval x):ℂ) • Glyph.preamblePl V p i x 0:= by
        rw [Finset.sum_eq_single (n,0)]; simp [oil,S,patch] -- check
        · intro j hj hne; by_cases h : j.1=n; · obtain ht:=mem_antidiagonal.mp hj; exact (hne (Prod.ext h (by dsimp; omega))).elim
          simp_rw [oil, show S j.1= A j.1 from patch_bef A Q X h,sub_self,zero_smul]
        simp
   rw [scorePl,scorePl,Pi.add_apply,Pi.add_apply, add_sub_add_comm,lightingPl]; congr 1
   · unfold rentPl; simp_rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _; rw [← hs c]; exact Finset.sum_congr rfl (fun k _=> (sub_smul (oil A c k.1 x) (oil S c k.1 x) (Glyph.preamblePl V p c x k.2)).symm)
   rw [sky, sky, add_sub_add_comm, ← map_sub,hc,advance]; congr 1
   rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0,n)]; dsimp only; rw [← map_sub,hc, style,whoZero]; -- check
   · intro j hj hne; obtain h :=mem_antidiagonal.mp hj; have h' : j.2≠n:= fun g=> hne (Prod.ext (by dsimp; omega) g); rw [patch_bef _ _ _ h', sub_self]
   simp
end YM.MS.Menus

-- Menus/Quantify
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : RichBook B)(p:Team) {d n r:ℕ}{v:ℤ}
namespace Glyph
variable {P S:ℝ→ Law G} {Q:Price B d}
lemma hitsPl (h: Homes Q v r)(x:ℝ) : Limit (lightingPl V p Q x).val r ∧ Fits (lightingPl V p Q x) (valAt Q x) r v false:= by
    refine ⟨?_,Fits.sum _ (fun i _=>?_)⟩; swap
    · by_cases he: Q i=0; · simp only [he,Polynomial.eval_zero,Complex.ofReal_zero]; rw [zero_smul,zero_smul]; exact Fits.zero _
      rw [← h.size i he, ← h.grade i he]; exact (Glyph.pre_floorPl V p i x).smul _
    unfold lightingPl; rw [sum_stack]; refine Limit.sum _ fun c _=>?_ ; by_cases he: Q c=0; rw [he,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=> rfl; rw [← h.grade c he]; exact Limit.smul _ ((by simpa using pre_costPl V p c x 0) : Limit (preamblePl V p c x 0).val c.grade)
end Glyph
structure CapacityPl (A C:Acts B d)(n r:ℕ)(v:ℤ) (H:ℝ→ Law G): Prop where
    past (i:ℕ): i<n→ A i=C i
    size (x:ℝ): Limit ((scorePl V p A x n)-(scorePl V p C x n)).val r
    jet (x:ℝ): Fits ((scorePl V p A x n)-(scorePl V p C x n)) (H x) r v false
-- permits leading reservation: if at order0 and r below highest rank the parameters are special. Later.
lemma room_herePl (A:Acts B d) {P H:ℝ→ Law G}(h:0≤v)(ht:v≤d)(hp:Ready P)(hq:Ready H) (hc : ∀ i,P i∈B.carries v r)(hd:∀ i,H i∈ Lease G (v-1) r (-1)): ∃ (Q:Price B d) (X:Power G), Glyph.Homes Q v r ∧ X.allowance=r ∧ CapacityPl V p A (patch A Q X n) n r v (fun i=> P i+natQ (H i)):= by
    obtain ⟨Q,hQ,hF⟩:= Glyph.offered h ht hc hp; obtain ⟨X,hx,hX⟩:= pens hq hd; have he (x:ℝ): Limit (advance (X.input x)).val r∧ Fits (advance (X.input x)) (natQ (H x)) r v false:= estimateL x (hx ▸ X.ranks x) (hX x)
    refine ⟨Q,X,hQ,hx,⟨fun i h=> (patch_bef A Q X h.ne).symm, fun x=>?_, fun x=>?_⟩⟩ <;> rw [repairPl]; exact (Glyph.hitsPl V p hQ x).1.add (he x).1; rw [← hF x]; exact (Glyph.hitsPl V p hQ x).2.add (he x).2
end YM.MS.Menus

-- Wind/Clone
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
variable {B: Local.Physical.Deck G} (W:RichBook B)
-- mark with canonical action; uses all t, 'A arbitrary finite dimensions.'
def horizonPl (W:RichBook B)(p:Team)(A:Acts B d): Dec G:= (member (skyPC G p) (decorPl W p A)).choose
lemma aquaPl (W: RichBook B)(p:Team)(A:Acts B d): PM (scorePl W p A) (skyline G p) (horizonPl W p A) 0 := (member (skyPC G p) (decorPl W p A)).choose_spec
lemma money_beforePl (A C:Acts B d)(h:∀ i<k,A i=C i) : ∀ i<k,horizonPl W p A i=horizonPl W p C i:= mark_birth (aquaPl W p A) (aquaPl W p C) (fun j hj x=> steadyPl W p A j C (fun i hi=>h i (by omega)) x) -- order of steadyPl args?
lemma mark_payPl {Z:ℝ→ Law G}{A C:Acts B d}(hf:CapacityPl W p A C k r u Z): Knick (horizonPl W p A k) (horizonPl W p C k) r u false Z:= by
    let T:= horizonPl (d:=d) W p; let F':=skyline G p; have he: path 1 k 0 F' (T A)=path 1 k 0 F' (T C):= path_eq _ _ _ (fun _ _=>rfl) (fun i hv=> money_beforePl W A C hf.past _ (path_in hv).2)
    refine knick ((aquaPl W p A).owes k) ((aquaPl W p C).owes k) ((aquaPl W p A).recu k) (fun x=>?_) hf.jet hf.size; rw [he]; exact (aquaPl W p C).recu k x
end YM.MS.Wind

-- Wind/Portfolio
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {U:ℕ→Type}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
variable {B:Deck G}(W: RichBook B)
def SeekPl (W: RichBook B)(p:Team)(d:ℕ): Knobs (fun _=> Tact B d) G where
   wake A:= col (horizonPl W p A)
   stay A C i h:= by funext y; unfold col; rw [money_beforePl W A C (k:=i+1) (fun j hj=>h j (by omega)) _ (by omega)]
lemma mark_seekPl (h: G.Simple): Marked (SeekPl W p d) (col (skyline G p)) B d where
    law A:= PMSolve h (skyPC G p) (aquaPl W p A) (decorPl W p A) (fun x=> lawPl W p x A h)
    occurs A:= post_ok _ (aquaPl W p A).owes
    moves A i r v hv ht a b hp hq hk hK:= by
       obtain ⟨Q,X,H1,H2,H⟩:= room_herePl (n:=i) W p A hv ht hp hq hk hK; exact ⟨_,rewind (K:=SeekPl W p d) (hp:=A) (hq:=Menus.patch A Q X i) rfl rfl H.past (fun x=>(((aquaPl W p A).owes i).stay x).joint) (fun x=> (((aquaPl W p _).owes i).stay x).joint) (mark_payPl W H)⟩
end YM.MS.Wind

-- Wind/Lead
namespace YM.MS.Wind.Leading
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p:Team}{B:Deck G}{d:ℕ}(V: RichBook B)(j:Glyph B d){F:Tact B d}{P: Acts B d}{n r:ℕ}{u:ℤ}
def trioPl (p:Team) : Knobs (Tactic0 j) G where
    wake P:= (SeekPl V p d).wake (clockM j P)
    stay _ _ _ h:=(SeekPl V p d).stay _ _ _ (fun i hi=>congr_arg Subtype.val (h i hi))
section fits
variable (p) {j}
lemma cap0Pl (h: FitOrder j (P 0))(x:ℝ) : Limit (scorePl V p P x 0).val j.grade ∧ Fits (scorePl V p P x 0) j.read j.grade j.size false:= by
   let A0:=scorePl V p P x 0; let f (c:Glyph B d):= oil P c 0 x • Glyph.preamblePl V p c x 0; let Y:Finset (Glyph B d):=Finset.univ.erase j; let Z:=Glyph.preamblePl V p j x 0; let T:= motto p P x 0; let U:= T + ∑ i∈Y,f i; have he : A0= Z+U:= by
       unfold A0 scorePl U T; rw [Pi.add_apply, add_left_comm,add_comm]; congr 1; unfold Menus.rentPl; simp_rw [Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; change ∑ c,f c=Z+∑ c∈Y,f c;
       rw [← Finset.add_sum_erase _ f (Finset.mem_univ j)]; unfold f oil; rw [h.Single j (le_refl _), if_pos rfl,Polynomial.eval_one,Complex.ofReal_one]; rw [one_smul]
   have hr : Limit T.val ((j.grade:ℤ)-1):= by
       have hl := h.Low x; let Q :=(P 0).proof; have hh:T= Menus.advance (Q.input x):= by simp only [T,sky,Finset.Nat.antidiagonal_zero,Finset.sum_singleton, style,whoZero]; rfl
       rw [hh]; exact Limit.add (Limit.up (lapLimit hl) (by omega)) (Limit.up (rootLimit (participates G 0) hl) (by omega)) -- root found Lifting
   have hi i (hi:i∈Y): Limit (f i).val ((j.grade:ℤ)-1):= by
       rcases lt_or_ge i.grade j.grade with hI|hI; · exact Limit.up (Limit.smul _ (Glyph.pre_costPl V p i x 0)) (by omega)
       unfold f oil; rw [h.Single i hI,if_neg (Finset.mem_erase.mp hi).1,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=>rfl
   have hL : Limit U.val ((j.grade:ℤ)-1):= by refine Limit.add hr ?_; rw [Cylinder.sum_stack]; exact Limit.sum _ hi
   rw [show scorePl V p P x 0=_ from he]; refine ⟨Limit.add (by convert Glyph.pre_costPl V p j x 0 using 1; simp) (Limit.up hL (by omega)),?_⟩; suffices ht : Fits U 0 j.grade j.size false from by rw [← add_zero j.read]; exact (Glyph.pre_floorPl V p j x).add ht
   unfold Fits; rw [maskOff (by omega) (Tone.oneRank hL)]; exact face_zero _
lemma zerosOrderPl (h:FitOrder j (P 0))(x:ℝ) : let U:= horizonPl V p P 0 x; Rank U j.grade ∧ ∀ t,Lifting.Face wfield (Book.mask j.grade (U t)) j.read j.size false:= by
   intro U; let M:= (aquaPl V p P); obtain hz:= M.recu 0 x; obtain hx := cap0Pl p V h x; change U 0 = _ ∧ _ at hz;
   have hv: Wind.Near false U:= by obtain ⟨r,hr⟩:= (M.owes 0).pay; refine ⟨((M.owes 0).stay x).joint,⟨r,hr x⟩,fun t w _=>?_⟩; have hl:=hz.2 t w; simpa only [Pi.add_apply, Wind.path,Domain.paths,Finset.Ico_self,Finset.sum_empty,smul_zero,Pi.zero_apply,add_zero] using hl
   obtain ⟨h0,hg⟩:= Dprecise hv (r:=j.grade) (hz.1 ▸ oneRank hx.1); refine ⟨h0,fun t=>?_⟩; rw [show Book.mask _ (U t)=Book.mask _ (U 0) from ?_,hz.1]; exact hx.2; funext w; by_cases he:(w.length:ℤ)=j.grade; simp only [enough _ he,hg w he]; simp only [strange _ he]
end fits
end YM.MS.Wind.Leading

-- Wind/MatchM
namespace YM.MS.Wind.Leading
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real Domain
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p:Team}{B:Deck G}{d:ℕ}(V: RichBook B){j:Glyph B d}{F S:Recount G}{P: Acts B d}{n r:ℕ}{u:ℤ}
lemma guardedPl (p:Team)(hx:FitOrder j (P 0))(h: PhysicalHF j F)(hr:j.grade ≤ r)(ht:u≤d)(H: Disc false 0 S F 1 d)(y:ℝ): slice ((SeekPl V p d).wake P 0-F 0) false r u y=0:= by
    refine excuse (F:=(SeekPl V p d).wake P) ?_ ?_ ?_ ht y
    · intro x w hw i H; let L := (SeekPl V p d).wake P; have hh:= zerosOrderPl p V hx x.1
      obtain h1|h1:= lt_or_eq_of_le hr
      · rw [torch_piece w hw (L 0 x), torch_piece w hw (F 0 x), maskOff (v:=r) (by omega) (show Limit (L 0 x) j.grade from hh.1 (exp x.2)),maskOff (u:=j.grade) (by omega) (h.too x)] -- L unfolding rw
      have hc : Form j.read wfield (j.size:ℤ) false:= (lease_one.mp (lease_enough G (B.le (B.form _ _ _)))).2.1; rw [← h1] at hw; rw [torch_piece w hw (L 0 x), face_here (show Lifting.Face wfield (mask j.grade (L 0 x)) j.read j.size false from hh.2 (exp x.2)) (w:=w) (fun u=> Bool.noConfusion u) i (by rw [h.owns]; exact H),torch_piece w hw (F 0 x), h.top, hc.const_term w (fun v=> Bool.noConfusion v)]
    · exact fun x w=> ((aquaPl V p P).owes 0 |>.stay x.1).joint.routine _ _
    exact fun x w=> (H.master.road ℝ (ray w) 0 (Nat.zero_le _) (fun v=> Bool.noConfusion v) (fun v=> Bool.noConfusion v)).1 x

-- use at any fixed action. preserve leading.
theorem physicalAtPl (h:G.Simple)(hq:Fixed (col (skyline G p)) F true 4 1) (hh: Disc false 0 F S 1 d)(hx: PhysicalHF j S): ∃ A: Acts B d, FitOrder j (A 0)∧ Fixed (col (horizonPl V p A)) S false d 0:= by
    let K:=trioPl V j p; let W:= SeekPl V p d; let U:= Tactic0 j; let V0:= col (skyline G p); let T:= mark_seekPl V (p:=p) (d:=d) h -- implicit arg V? #error
    have HT (i:Code U): Spheres wave (spaceL G) V0 (K.wake i) 1 0 false:= T.law _;
    suffices he: ∃ i:Code U, Fixed (K.wake i) S false d 0 by obtain ⟨i,hi⟩:=he; exact ⟨clockM _ i,(i 0).property rfl,hi⟩
    refine assigned (B:=fun _=> V0) HT hh.master hh.good (fun i=>T.occurs (clockM j i)) hh.open' ?_ (by omega) ?_ (script j)
    · intro X n hn hp i hi r; exact hq (n-i) (by obtain he:=path_in hi; omega) _ (fun _ => Nat.succ_pos r)
    intro n hn r hr u hu hv X EE HE
    let M:= K.wake X n-S n; let J:= slice M false r u; have hz:= advanced (HT X) hh.master hn hr EE
    by_cases hk: n=0 ∧ j.grade≤r; · obtain ⟨rfl,H⟩:=hk; refine ⟨X, Move.refl J ?_ ⟩; intro i w _ hx'; change slice _ _ _ _ _ _=_; exact congr_fun (guardedPl V p (P:=clockM j X) ((X 0).property rfl) hx H hv hh i) w -- J after subst
    have ht : Ready J:= slice_ready hz hv (Ready.sub ((HT X).poly n) (hh.master.poly n));
    have hu' (i:ℝ) : J i∈ Lease G u r 0:= lease_one.mpr ⟨slice_solid hz hv fun t=> ((HT X).trueC n t).sub (hh.master.trueC n t),slice_form hz hv,rank_slice⟩
    have hL (i:ℝ) : natQ (J i)=0:= funext (fun l=> closes (HT X) hh.master hh.good hn hr EE hv HE i l (fun v=>Bool.noConfusion v))
    obtain ⟨a,g,h0,h1,hJ,hI,he⟩:= mark_inter ht hu' hL B; obtain ⟨Q,T,hQ,hT,hW⟩:= Menus.room_herePl (n:=n) V p (clockM j X) hu hv h0 h1 hJ hI
    let P := Menus.patch (clockM j X) Q T n; have he' : FitOrder j (P 0):= fix_order (P:=clockM j X) ((X 0).property rfl) hQ hT.le (by omega)
    let Y:Code U:= fun i=> ⟨P i,fun h=> h ▸ he'⟩;
    have hm : ∀ i<n,(X i)=(Y i):= fun i hi=> Subtype.ext (hW.past i hi)
    refine ⟨Y, Move.replace (rewind (K:=K) rfl rfl hm (fun i=> (((aquaPl V p (clockM j X)).owes n).stay i).joint) (fun i=> (((aquaPl V p P).owes n).stay i).joint) (mark_payPl V hW)) (fun i w hw hI=> congr_fun (congr_fun he i) w)⟩ -- removePl
end YM.MS.Wind.Leading

-- Mach/Land
namespace YM.MS.Land
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical -- Pole not opened yet
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{k m n h d:ℕ}{V:Box (Mob G)}{F H:ℂ→Mob G}{B:Deck G}
structure TaylorOKPl {A:Booked B}(M:MS_Data G A)(V:RichBook B)(S: Prescription B): Prop where
   bulk: Fixed (col ( skyline G S.team )) ( Archive 4 M.bulk ) true 4 1
   mark (d:ℕ) (i: Plaid B d): Fixed ( col (horizonPl V S.team (S.fees d i) )) ( Archive d (M.marks d i)) false d 0
variable (hc:G.Simple)
include hc
theorem High_stopsPl {A:Booked B}(X: MS_Data G A)(V:RichBook B): ∃ P: Prescription B,TaylorOKPl X V P:= by
    obtain ⟨p,H⟩:= leader_M hc B A X; have he d (i:Plaid B d):= physicalAtPl V (j:=read i) hc H ( Outlook.fieldD X.bulkOK (X.markOK d i) wisdom (( A.law d i).moodQ)) (initialHF (A.law d i) (sizeG i) (X.markOK d i)); choose S hs h using he; exact ⟨⟨ p,S,hs ⟩,⟨ H,h ⟩⟩
end YM.MS.Land
