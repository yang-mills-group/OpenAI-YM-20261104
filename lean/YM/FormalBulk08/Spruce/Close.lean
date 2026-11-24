import YM.FormalBulk08.Spruce.Nook
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X I J:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H:Hol G}
variable {ρ:ChartRatio G}{o:Loc G 1}{Y: X→ Anthem D G}
-- k−1 to k with scalar reexpression; on tie projection zero. heights concern only slot.

def signa (u:I→ℕ) (P: Matrix I J Pence)(l:ℕ):Prop:=∀ i j e,l+e<u i→ coeff e (P i j) = 0
lemma signa_zero (u:I→ℕ)(l:ℕ):signa u (0: Matrix I J Pence) l:= fun i j e _=>by simp
lemma signa_sum {P Q: Matrix I J Pence}{u:I→ℕ}(h:signa u P l)(p:signa u Q l): signa u (P+Q) l:= fun i j e ht=> by rw [Matrix.add_apply,map_add, h i j e ht,p i j e ht, add_zero]
lemma signa_mul [Fintype I][DecidableEq I]{P: Matrix I J Pence}{Q:Pennants I}{u w:I→ℕ}{b:I→ℝ}(h:signa u P l)(p:Colfax u w Q b): signa u (Q*P) l:= by
    intro i j e he; rw [Matrix.mul_apply, map_sum]; refine Finset.sum_eq_zero fun k _=>?_ ; rw [coeff_mul]; refine Finset.sum_eq_zero fun x hx=>?_ ; rw [Finset.mem_antidiagonal] at hx; by_cases hK:l+x.2<u k
    · rw [h k j _ hK,mul_zero]
    rw [p.bound i k x.1 (by omega),zero_mul]
lemma signa_val {P:Matrix I J Pence}{u:I→ℕ}(Q:Pence)(p: coeff 0 Q=0)(h:signa u P l): signa u (P.map (PowerSeries.subst Q)) l := by
    intro i j e he; rw [Matrix.map_apply,subst_coeff p _ e e le_rfl]; refine Finset.sum_eq_zero fun k hk=>?_ ; rw [Finset.mem_range] at hk;rw [h i j k (by omega),zero_mul]
-- avoid global chart dependencies, universal
lemma migrate_m (Y:Anthem D G)(P:Flight j t)(V:Lodge P.patch)(T:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(f:hue G)(o: Loc G 1)(hm:Wade o Y l)(hv:Vivid T)(hp:LocalRatio ρ)(hL:2≤P.L.val)(hx:l≤e)(d): migrates f P V K T ρ h hL d e Y=migrates f P V K T ρ h hL d l Y:= by unfold migrates;rw [quick_more P V ρ h hp hv hm hL e hx]
lemma larch_add [Fintype I](Y:I→ Anthem D G)(Q V:Matrix I J Pence): larch Y (Q+V)=larch Y Q+ larch Y V:=by funext j; unfold larch; rw [Pi.add_apply, ←Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>by rw [Matrix.add_apply, launch_add]
variable (l ρ T)(q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)
abbrev echoR (x:Turn C) := bornM (T:=T) (W:=W) (ρ:=ρ) a q.horizon x.a (P.N x.a) x.b
-- `C` implicit?
abbrev wrist (W:Lab G K X)(P: Pin W.scrolls)(z:X) (k:ℕ): Pence:= bandK ρ a W P.N z k

variable (Y: X→ Anthem D G)
def billing (x:X): ℕ→ Matrix (Letter F) Unit Pence
   | 0=>0
   | i+1=> if h:W.neck x ≤ i∧ i < C.N x then
       let z:Turn C:=⟨⟨x,i,h.1⟩,h.2⟩
       (((echoR T ρ q a C P z)⁻¹)*(feed (T:=T) l ρ q a C P z Y + billing x i)).map (PowerSeries.subst (wake (wrist ρ a W P x i)))
       else 0

-- when paying top sum, boundary A: projection even uppercase
lemma wrist_step (x:Turn C): wrist ρ a W P x.a x.b = epoch a (graded W.liftF (W.trail P.N) x) (W.liftU x) K (Lab.instory ρ a W P.N x.ups) ρ (W.liftH x) := rfl
abbrev debt (x:Deck C):= billing l T ρ q a C P Y x.a x.b
lemma fee (x:Turn C): debt l T ρ q a C P Y x.ups = ((echoR T ρ q a C P x)⁻¹ *(feed (T:=T) l ρ q a C P x Y+ debt l T ρ q a C P Y x.bed)).map (PowerSeries.subst (wake (wrist ρ a W P x.a x.b))) := by
    change billing _ T _ q a C P Y x.a (x.b+1)=_ ;rw [billing,dif_pos ⟨x.zone,x.head⟩]
lemma bills_empty (x:X)(i:ℕ)(h:i ≤ W.neck x): billing l T ρ q a C P Y x i=0:= by
    cases i with
    | zero=> rfl
    | succ i=> rw [billing,dif_neg (fun hx=>by omega)]
end YM.FormalBulk08.Spruce
