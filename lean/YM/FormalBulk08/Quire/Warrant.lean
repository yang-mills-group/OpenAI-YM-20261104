import YM.FormalBulk08.Quire.Audience
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge} {m d D l e r j t n :ℕ}{η σ A B C:ℝ}{P:Patch}{K:KernelChoices}{a:Loc G 1}
-- Any fixed datum step can price arbitrary length factors, hence local Qual. Just use singleton families.

def Qual (Y: Anthem D G)(o: Loc G 1)(E:ℕ)(η:ℝ) : Prop := ∀ e≤ E,∀ r,LightPay (fame _) η (0,o) (fun p=>Y p e r) (‖·‖)
lemma sectionQual (F:Frame G d)(T: SectionData F)(hd:d+1≤D)(i: Letter F)(o:Loc G 1)(E:ℕ)(η:ℝ): Qual (sectionY T hd i) o E η:= by
    intro e _ r; obtain ⟨C,H⟩:=hymn_bill (rancho (dabs T (mint F i)) e r) η (0,o); exact ⟨C,H.1,fun p=>(H.smul _).mono ((mul_le_mul_of_nonneg_right (notch_le _ p) H.1).trans_eq (mul_comm ..))⟩
lemma qual_sub {T S: Anthem D G}(h:Qual T a e η)(hy:Qual S a e η) : Qual (T-S) a e η := by
    intro i hi r; change LightPay _ η _ (fun p=> T p i r-S p i r) _; simp_rw [sub_eq_add_neg]; exact (h _ hi r).plus (by simpa only [neg_one_smul] using (hy _ hi r).amp (-1))
lemma qual_launch {T: Anthem D G}(h:Qual T a e η)(p:Pence): Qual (launch p T) a e η:= by
    intro i hi r; refine pay_sums (Finset.antidiagonal i) (fun j hj=>?_); rw [Finset.mem_antidiagonal] at hj; exact (h _ (by omega) _).amp _
lemma qual_larch {I J:Type*}[Fintype I](T:I→ Anthem D G)(M: Matrix I J Pence)(u:J)(h:∀ i,Qual (T i) a e η): Qual (larch T M u) a e η:= by
    intro i hi r; unfold larch; simp_rw [Finset.sum_apply]; exact pay_sums _ (fun i _=>(qual_launch (h i) _) _ hi r)

variable {X:Type}
def oneT : Time Unit := ⟨fun _=>1,fun _=>le_rfl⟩
lemma unit_soft (τ:Time Unit)(f:Unit→ℝ): Soft τ f:=(soft_coin τ (f ())).below (fun i=>by rw [show i=() from Subsingleton.elim ..])
lemma unit_pact (τ:Time Unit)(f g δ:Unit→ℝ)(h:f=g): Pact τ δ f g:= h ▸ Pact.constant (unit_soft τ _)
lemma unit_tender (τ:Time Unit)(a:Loc G 1)(Y:Unit→Studio D→Tile (edgeL G) r)(η: Unit→ℝ): Tender τ a η (fun _=>1) Y ↔ LightPay (fame _) (η ()) (0,a) (Y ()) (‖·‖):=by
    constructor
    · intro h; obtain ⟨K,k,h,H⟩:= h; exact ⟨_,h (),fun p=>by simpa only [one_mul] using H () p⟩
    intro h; obtain ⟨C,c,H⟩:=h; exact ⟨fun _=> C,soft_coin τ C,fun _=> c,fun i p=> by rw [show i=() from Subsingleton.elim ..]; simpa only [one_mul] using H p⟩
lemma toW (Z : Flight j t)(S:Lodge Z.patch)(o:hue G)(ρ:ChartRatio G)(h:Z.patch.Branches K G)(hp:LocalRatio ρ)(ht:4≤t)(hs:0<σ)(hη:0<η)(hz:η≤Z.L.val*σ)(W:Pot G)(HE: Story W (pink K.penalty Z.wing))(E:ℕ) (hx:∀ e≤ E,∀ k,∃ B:ℝ,Bail (fame _) σ (W e k) B)
     (hZ:(locating G K Z S).strip η A)(hr:(gamma G K Z S h).strip η B)(hc:0≤A)(hb:0≤B) : Wells oneT (fun _=> Z) (fun _=> S) (fun _=> h) ρ o (fun _=>σ) (fun _=>η) 0 (fun _=> Z.wing) (fun _=> Z.wing) (fun _=> W) (fun _=>W) E:= by
    let P: Unit→Flight j t:= fun _=>Z
    have he (i:Unit):graded P (fun _=> Z.wing) i=Z:= rfl
    refine ⟨⟨fun _=>hz,fun _=>hs,fun _=>hη,soft_coin _ _, soft_coin _ _, soft_coin _ _,soft_coin _ _,?_,?_⟩,Honest.mock ?_,fun i=>le_rfl,soft_coin _ _,hp,fun _=>HE,fun _=>HE,?_,fun _=>ht,?_⟩
    · intro e he hi r hr hb; obtain ⟨C,hC⟩:=TO_bail G e r η Z.patch K; exact ⟨fun _=> C,soft_coin _ _,fun _=>hC⟩
    · intro e he hi r hr hb; obtain ⟨C,hC⟩:=WO_bail G e r η S ρ; exact ⟨fun _=>C,soft_coin _ _,fun _=>hC⟩
    · exact ⟨⟨fun _=>A,soft_coin _ _,fun _=>hc,fun i=> hZ⟩,⟨fun _=>B,soft_coin _ _,fun _=>hb,fun i=>hr⟩⟩
    · intro i hi k; obtain ⟨C,hC⟩:=hx i hi k; exact Totem.constant ⟨fun _=> C,soft_coin _ _,fun _=> hC⟩
    exact fun i _=> Pact.constant (unit_soft oneT _)
lemma migrate_qual (Z:Flight j t)(S:Lodge Z.patch)(o:hue G)(ρ:ChartRatio G)(h:Z.patch.Branches K G)(T:Anthem D G)(hp:LocalRatio ρ)(ht:4≤t)(hs:0<σ)(hη:0<η)(hz:η≤Z.L.val*σ)(W:Pot G)(HE:Story W (pink K.penalty Z.wing)) (E:ℕ)(hx:∀ e≤E,∀ k,∃ B:ℝ,Bail (fame _) σ (W e k) B)(hZ:(locating G K Z S).strip η A)(hr:(Flat.gamma G K Z S h).strip η B)(hc:0≤A)(hb:0≤B)(hL:2≤Z.L.val)(d u)(hy:Qual T a E σ):
     Qual (migrates o Z S K W ρ h hL d u T) a E η:= by
    have hw:=toW Z S o _ h hp ht hs hη hz W HE E hx hZ hr hc hb; intro i hi r
    have hh j (hj:j ≤ E)(k:ℕ): Brass oneT a (fun _=>σ) 0 (fun _=>1) (fun _ p=> T p j k) (fun _ p=>T p j k):= Matched.constant ((unit_tender oneT a _ _).mpr (hy j hj k))
    have H:= Matched.left (full_income (T:=fun _=> T) (S:=fun _=>T) hw (fun _=>zero_le_one) (fun _=>hL) d u i r hi (fun j k hj=> hh j (by unfold precede at *;omega) k) (hh i hi r))
    exact (unit_tender oneT a _ _).mp H
end YM.FormalBulk08.Quire
