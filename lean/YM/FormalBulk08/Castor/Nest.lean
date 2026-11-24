import YM.FormalBulk08.Castor.Fossil
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{d D l r e k m j t:ℕ}{ρ:ChartRatio G}{Z:Frame G d}{B:Frame G m}{T:Anthem D G} {o: Loc G 1}

def smaller (L:Side) (h H:ℕ) := ((L.val:ℝ)^(H-h))⁻¹
lemma small_le (L:Side)(h H:ℕ):|smaller L h H|≤1:= by rw [abs_of_nonneg (by unfold smaller; positivity)]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (Nat.one_le_cast.mpr L.property))
lemma immune (L:Side)(h:k≤ m) : aven L k= smaller L k m * aven L m:= by rw [aven, smaller,aven,show (L.val:ℝ)^m=(L.val:ℝ)^k*(L.val:ℝ)^(m-k) from (by rw [←pow_add,Nat.add_sub_of_le h])]; field_simp
-- pay scaling. No reference-coordinate identification assumed even across same terminal.
lemma points (ρ:ChartRatio G)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)(Y:Anthem D G)(hs:LocalRatio ρ)(he:Vivid W)(hp:k≤m)(ht:Clef o Y k):
    migrates a P V K W ρ h hL k k Y=smaller P.L k m • migrates a P V K W ρ h hL m m Y:= by
    unfold migrates stir; rw [quick_more P V ρ h hs he ht.fare hL m hp]; funext p e r
    unfold Wine.stamp quick; nth_rw 1 [immune P.L hp]; simp only [Pi.smul_apply,Finset.sum_apply,mul_smul,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [smul_comm (Wine.bill ..)] -- hly
variable (ρ)(a:hue G)(P:Flight j t)(V:Lodge P.patch)(h:P.patch.Branches K G)(hL:2≤P.L.val)(W:Pot G)
   (hs:LocalRatio ρ) (he:Story W (pink K.penalty P.wing))(ht:4≤ t)
include hs he ht
lemma repl (Y Y' : Roof.Plaza Z D)(hY:Court o Z Y)(hp:Court o Z Y') (U: Tilework Z) (hz:migrates a P V K W ρ h hL d d ∘ Y=larch Y' U)(X:Anthem D G)(hx:Clef o X d): canopy Z Y' (migrates a P V K W ρ h hL d d X) = canopy Z Y' (migrates a P V K W ρ h hL d d (canopy Z Y X)):= by
    let T:=fun _:Unit=>X; let A:=pantry Z T; let M:=migrates (D:=D) a P V K W ρ h hL d d; let R:=canopy Z Y X; let V':=crease Z Y X; have H0:R+V'=X:=sub_add_cancel ..
    have hr := (canopy_nav hY hx).1; have hv:= crease_cleans hY hx; change canopy _ _ (M X)=canopy _ _ (M R)
    rw [←H0,show M (R+V')=M R+M V' from migrate_add a _ _ d hr.fare hv.fare he ht hs le_rfl,sail_can hp (migrate_w a h hL d hr he ht hs le_rfl) (migrate_w a h hL d hv he ht hs le_rfl), show canopy Z Y' (M V')=0 from ?_,add_zero]
    apply Eq.trans ?h (show canopy Z Y' (larch Y' (U * A.map (Roof.reborn a P V K W ρ h)) ())=0 from congr_fun (departure hp) ()); apply congr_arg
    have heq : M ∘ larch Y A = larch (M ∘ Y) (A.map (Roof.reborn a P V K W ρ h)) := hammers ρ a P V h hL W o d d Y A (fun i=> (hY.officers i).fare.through (slotsFits ..)) he ht hs
    rw [show M ∘ Y=_ from hz,larch_circuit] at heq; exact congr_fun heq ()
lemma captured (h':m≤ d)(Y Y': Roof.Plaza Z D)(hY:Court o Z Y)(hp:Court o Z Y')(U : Tilework Z) (hz:migrates a P V K W ρ h hL d d ∘ Y= larch Y' U) (X X': Roof.Plaza B D)(hX:Court o B X)(hx:Court o B X') (S:Tilework B)(hS:migrates a P V K W ρ h hL m m ∘ X=larch X' S) (x:Letter B):
   larch (canopy Z Y' ∘ X') S x=smaller P.L m d • canopy Z Y' (migrates a P V K W ρ h hL d d (canopy Z Y (X x))):= by
   let M:=migrates (D:=D) a P V K W ρ h hL d d; have hA:= clef_through (hX.officers x) (slotsFits B x); have hv:= clef_through hA h'
   rw [← recup X' S hp (fun i=> (hx.officers i).fare.through (slotsFits ..)),←hS]; simp only [Function.comp_apply]; rw [points ρ a P V h hL _ _ hs he.toVivid h' hA, decay_scale _ (migrate_w a h hL _ hv he ht hs le_rfl).fare,repl ρ a P V h hL _ hs he ht Y Y' hY hp U hz (X x) hv]
end YM.FormalBulk08.Castor
