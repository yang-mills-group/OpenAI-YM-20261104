import YM.FormalBulk08.Quire.Moral
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge} {m d D l e r j t n :ℕ}{η σ A B C:ℝ}{P:Patch}{L:Side}{K:KernelChoices}
structure Office (K:KernelChoices)(F: Frame G d)(a:Loc G 1)(η σ :ℝ)(Z:Flight j t)(U:Lodge Z.patch)(e r l D:ℕ)(μ X:ℝ):Prop where
    plea : ∀ T:Anthem D G,Clef a T l → ∀ B:ℝ,Deposit a η T e B → (∀ i,‖coeff e (echo F T i)‖ ≤ B) → ∀ A:ℝ, 0≤A → (∀ p,Knoxville (fame _) η (0,a) (T p e r) (A*‖p‖)) → ∀ hL:2≤Z.L.val, (∀ i:Letter F, slots F i=r → ‖pearlJ F (blade Z K U T d e r hL (inside F i D)) (mint F i)‖ ≤ X*B) ∧ ∀ p, Knoxville (fame _) σ (0,a) (blade Z K U T d e r hL p) ((μ*A+X*B)*‖p‖)
lemma renders {Z:Flight j t}{U:Lodge Z.patch}{F:Frame G d}{a:Loc G 1}(x h:ℝ)(hp:Office K F a σ η Z U e r l D x A)(hv:A≤B)(he:x≤h): Office K F a σ η Z U e r l D h B:= by
     refine ⟨fun Y hY b hg hz a' ha' H hL=>?_⟩; obtain ⟨z,t⟩:=hp.plea Y hY b hg hz a' ha' H hL; exact ⟨fun i hi=>(z i hi).trans (mul_le_mul_of_nonneg_right hv hg.1),fun p=>(t p).mono (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right he ha') (mul_le_mul_of_nonneg_right hv hg.1)) (norm_nonneg _))⟩
structure Penny (F:Frame G d)(o:Loc G 1)(σ B:ℝ)(r:ℕ):Prop where
    pays : ∀ X:Tile (edgeL G) r,∀ A, Knoxville (fame _) σ (0,o) X A → ∀ i:Letter F, ‖pearlJ F X (mint F i)‖ ≤ B*A
lemma penny_use (F:Frame G d)(o:Loc G 1)(h:0<σ)(r):∃ C:ℝ,0<C ∧ Penny F o σ C r:= by
    choose c hc H using fun i: Letter F=> pearl_cost F o i r h; let B:=∑ i,c i; have hB:0 ≤ B:=Finset.sum_nonneg (fun _ _=>hc _); refine ⟨1+B,add_pos_of_pos_of_nonneg one_pos hB,⟨fun X A hx i=>?_⟩⟩; exact (H i X A hx).trans (mul_le_mul_of_nonneg_right (le_trans (show c i≤B from Finset.single_le_sum (fun j _=>hc j) (Finset.mem_univ i)) (le_add_of_nonneg_left zero_le_one)) hx.1)
lemma penny_raise {F:Frame G d}{a:Loc G 1}(h:Penny F a σ A r)(he:A≤B): Penny F a σ B r:= ⟨fun X W hx i=> (h.pays X W hx i).trans (mul_le_mul_of_nonneg_right he hx.1)⟩
-- Audience on P AFTER. lengths PRE from fFormal patch; T axes use only finite ℓ arity
structure Lecture (K:KernelChoices)(F:Frame G d)(o:Loc G 1)(D E R j t:ℕ)(σ η:ℝ)(P:Patch)(V:Lodge P)(B:ℝ):Prop where
    plus:0≤B
    pupils : ∀ r≤R+E,Penny F o η B r
    bill : ∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ h:Z.patch=P,h ▸ U=V → ∀ e≤E,∀ r≤R+E,∀ l≤R,Office K F o σ η Z U e r l D (Dove.Mulct Z.L) B
lemma lecture_raise {F:Frame G d}{o:Loc G 1}{U:Lodge P}(h:Lecture K F o D e r j t σ η P U A)(p:A≤B): Lecture K F o D e r j t σ η P U B:= ⟨h.plus.trans p,fun i hx=>penny_raise (h.pupils i hx) p,fun Z S _ hz i hi Y hs k hp=>renders _ _ (h.bill Z S _ hz i hi Y hs k hp) p le_rfl⟩
def Passage (K:KernelChoices)(F:Frame G d)(o:Loc G 1)(D E R j t:ℕ)(σ η B:ℝ):Prop:= ∀ P:Patch,B≤(P.L.val:ℝ) →∀ V:Lodge P, ∃ C:ℝ,Lecture K F o D E R j t σ η P V C
lemma passage_pre (K:KernelChoices)(F:Frame G d)(H:Hol G)(o:Loc G 1)(D E R j t:ℕ)(h:d<D)(hj:4≤ j)(hp:d+1≤j-2) (ht:4≤t)(hs:0<σ)(he:0<η)(hw:∀ P:Flight j t,RepeatPrices K.penalty η C P)(hc:0≤C): ∃ B:ℝ, Passage K F o D E R j t σ η B:= by
    let I := Fin (E+1)×Fin (R+E+1)×Fin (R+1)
    choose! B hB Hx using fun i:I=> moral o F H i.2.1.val i.2.2.val i.1.val D h hj hp ht hs he hc K
    let B':=∑ i,B i
    refine ⟨B',fun P hz V=>?_⟩; choose! C' hc' H' using fun i=> Hx i P ((Finset.single_le_sum (f:=B) (fun j _=> hB j) (Finset.mem_univ i)).trans hz) V
    let X:= ∑ i,C' i; choose! A hA HA using fun i:Fin (R+E+1)=>penny_use F o he i.val; let M:= ∑ i,A i; have hh:0≤X:=Finset.sum_nonneg (fun _ _=>hc' _); have hM:0≤M:= Finset.sum_nonneg (fun _ _=> (hA _).le)
    refine ⟨X+M, add_nonneg hh hM,fun i hi=> ?_,fun Z U h hv e he r hr l hl=>?_⟩
    · let z: Fin (R+E+1):= ⟨i,by omega⟩; exact penny_raise (HA z) ((show A z≤ M from Finset.single_le_sum (fun i _=>(hA i).le) (Finset.mem_univ z)).trans (le_add_of_nonneg_left hh))
    let z : I:=(⟨e,by omega⟩,⟨r,by omega⟩,⟨l,by omega⟩); exact renders _ _ (show Office K F o σ η Z U e r l D (Dove.Mulct Z.L) (C' z) from ⟨H' z Z U _ hv (hw Z)⟩) ((show C' z ≤ X from Finset.single_le_sum (fun i _=> hc' i) (Finset.mem_univ z)).trans (le_add_of_nonneg_right hM)) le_rfl

-- use flat may-use theorem directly (proof price depends on t,j only).
def coverPrice (G:Gauge)(K:KernelChoices)(j t:ℕ):ℝ:= if h:4≤j∧ 4≤t then (may_use G K j t h.1 h.2).choose else 1
lemma pricePlus (G:Gauge)(K:KernelChoices)(j t:ℕ) : 0<coverPrice G K j t:= by
   unfold coverPrice;split; next h=> exact ((may_use G K j t h.1 h.2).choose_spec.choose_spec.1)
   next=>norm_num
lemma purchase (K:KernelChoices)(F:Frame G d)(H:Hol G)(o:Loc G 1)(D E R j t:ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤t)(hs:0<σ)(he:0<η)(hw:η≤coverPrice G K j t):∃ B:ℝ,Passage K F o D E R j t σ η B:= by
    rw [coverPrice,dif_pos ⟨hj,ht⟩] at hw
    obtain ⟨C,hC,b,H',-⟩:=(may_use G K j t hj ht).choose_spec
    exact passage_pre K F H o D E R j t h hj hp ht hs he (fun V l he=> ⟨strip_mono (H' V l he).1 hw le_rfl,strip_mono (H' V l he).2 hw le_rfl⟩) b.le
end YM.FormalBulk08.Quire
