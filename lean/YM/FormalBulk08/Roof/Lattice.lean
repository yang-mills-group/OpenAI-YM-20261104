import YM.FormalBulk08.Roof.Axle
import YM.FormalBulk08.Aster.Lender

/-! The field step in the *new* local formal variable. Include semantic transfers
on power series with scalar accounting. Rectangular alphabet possible. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I J: Type*}{K:KernelChoices}{n m l e u r j t D:ℕ}{x:Loc G 1}{W:Pot G}{Y:Anthem D G}

lemma cap_braise (P:Flight j t) (V:Lodge P.patch)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hr:LocalRatio ρ)(hp:Vivid W)(Z:Pot G)(ht:Young Z l)(u)(hu:l≤u) : braise P V W Z ρ h u= braise P V W Z ρ h l:= by
   funext i k; unfold braise; symm;refine Finset.sum_subset (Finset.range_mono (by omega)) fun q _ hs=>?_; have hv : border P V W Z ρ h q i k=0:= by by_contra hh; have hz:= (youth_egg _ (convict (K:=K) P V Z ht) (fairy W ρ P V K hp hr) q i k hh).2; simp only [Finset.mem_range,not_lt] at hs; omega
   rw [hv,jetty_zero]
lemma quick_more (P:Flight j t)(V:Lodge P.patch)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hr:LocalRatio ρ)(hp:Vivid W)(hy: Wade x Y l)(hL:2≤P.L.val)(u)(he:l≤u)(d): quick P V W Y ρ h hL d u=quick P V W Y ρ h hL d l:= by
    funext p; unfold quick;apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; exact cap_braise P V _ _ hr hp _ (step_can x P Y hy hL p i) _ he
variable (a:hue G)(P:Flight j t)(V:Lodge P.patch)(K:KernelChoices)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G) (hL:2≤P.L.val) (d:ℕ)
-- choice noise state exact
def epoch : Pence := Wine.scalar a (waken P V W ρ h)
def migrates (l:ℕ)(T:Anthem D G) : Anthem D G:=
   stir (bookH (epoch a P V K W ρ h)) (bookU (epoch a P V K W ρ h)) (quick P V W T ρ h hL d l)

def reborn : Pence →+*Pence:= (substAlgHom (R:=ℝ) (tribe (runic_phi (epoch a P V K W ρ h)))).toRingHom
lemma rele (p:Pence): Roof.reborn a P V K W ρ h p=p.subst (bookH (epoch a P V K W ρ h)*X):=by
   unfold Roof.reborn; rw [mul_comm,forward_green]; change substAlgHom (R:=ℝ) _ p=_; rw [coe_substAlgHom]

variable {K P V W ρ}
lemma migrate_w (hy:Clef x Y l)(hw:Story W (pink K.penalty P.wing))(hs:4≤ t)(hr:LocalRatio ρ)(hu:l≤u): Clef x (migrates a P V K W ρ h hL d u Y) l:= by unfold migrates; rw [quick_more P V ρ h hr hw.toVivid hy.fare hL u hu]; exact (linear_step x P V Y _ ρ h hy hw hr hL hs d).stirs (book_equal _)
lemma migrate_plus (p:Pence)(hy: Wade x Y l)(hw:Story W (pink K.penalty P.wing))(hs:4≤t)(hr:LocalRatio ρ)(he:l≤u) : migrates a P V K W ρ h hL d u (launch p Y)= launch (Roof.reborn a P V K W ρ h p) (migrates a P V K W ρ h hL d u Y):= by
   unfold migrates;rw [funext (fun z=> quick_pact x P V W _ h hy hw hr hL hs he z d p),stir_worm _ _ _ (quick_Wade x P V Y W ρ h hy hw hr hL hs he _), rele]
lemma migrate_add {T:Anthem D G}(hy: Wade x Y l)(ht: Wade x T l)(hw:Story W (pink K.penalty P.wing))(hs:4≤t)(hr:LocalRatio ρ)(he:l≤u): migrates a P V K W ρ h hL d u (Y+T)=migrates a P V K W ρ h hL d u Y+migrates a P V K W ρ h hL d u T:= by
    unfold migrates; have ht':quick P V W (Y+T) ρ h hL d u=quick P V W Y ρ h hL d u + quick P V W T ρ h hL d u := funext fun z=>quick_pair x P V W _ h hy hw hr hL hs he ht _ d; rw [ht']; exact stir_add ..
lemma migrant_zero (x:Loc G 1)(l:ℕ)(hw:Story W (pink K.penalty P.wing))(hs:4≤t)(hr:LocalRatio ρ): migrates a P V K W ρ h hL d l (0: Anthem D G)=0:= by
   have hh:=migrate_plus (d:=d) (ρ:=ρ) (K:=K) (u:=l) (V:=V) a h hL 0 (wade_zero (a:=x) (l:=l) (D:=D)) hw hs hr le_rfl; rwa [void_launch,map_zero,void_launch] at hh
end YM.FormalBulk08.Roof
