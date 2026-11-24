import YM.FormalBulk08.Cork.Cents

/-! Readout rank and displacement valuation. This matches affine-null on
potential tensors, thus removes dependence on an inherited cochain lift. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}
lemma nonempty_color (h:G.Simple): Nonempty (hue G):= by
    haveI ht:= h.nontrivial_color
    cases isEmpty_or_nonempty (hue G) with
    | inl he=> obtain ⟨x,y,hp⟩:=exists_pair_ne G.Color; exact False.elim (hp (by ext i; exact IsEmpty.false i|>.elim))
    | inr he=> exact he

-- Price in given width incl parallel; want post for α, but diagonal rank uses extraction
-- from inherited gain BEFORE-L; powers are pre.
lemma priced_hook {σ : ℝ} (hs:0<σ) : ∃ C : ℝ,0<C ∧ ∀ A (T : Slopes G), Bail (fame _) σ T A → ∀ i, |value i T| ≤ A*C := by
    obtain ⟨n,D,hd⟩:= (Pad.ch 0).mul (Pad.ch 0); obtain ⟨C,hC,H⟩:= net_funding (G:=G) n hs
    exact ⟨max 1 (D*C),lt_max_of_lt_left one_pos,fun A T h i=> (H _ _ hd T _ h 1 1 i i).trans (mul_le_mul_of_nonneg_left (le_max_right ..) h.1)⟩
lemma value_add {T R : Slopes G}(h:Purse T)(e:Purse R)(i): value i (T+R)=value i T + value i R:= net_add h e _ _ _ _ ((Pad.ch 0).mul (Pad.ch 0))
lemma value_less {T R : Slopes G}(h:Purse T)(e:Purse R)(i): value i (T-R)=value i T - value i R:= net_sub h e _ _ _ _ ((Pad.ch 0).mul (Pad.ch 0))
lemma value_coin (T : Slopes G) (c : ℝ) (i):value i (c • T)=c*value i T:= net_smul c T ..
structure Null (T:Slopes G) : Prop where
    bottom : ∀ b a i j, net T b a i j 1=0
    air : ∀ b a i j u, net T b a i j (ch u)=0
    water : ∀ b a i j u v, mir T b a i j u v=0
lemma direct_nil {T : Slopes G}(h:Splendid T)(hs:G.Simple)(i:hue G)(he:value i T=0):Null T:= ⟨fun a b=>direct_zero h.gradient h.fares b a, direct_line h.gradient h.worn h.up h.fares, all_caps h fun a b k j h' => (tag_rule h a b h' k j 1 0 (by decide)).trans (detects h hs _ _ he k j)⟩
lemma charge_nil {T S: Slopes G}(h:Splendid T)(e: Splendid S)(i:hue G)(hz:value i S=1)(hs:G.Simple): Null (T-value i T • S):= direct_nil (splendid_sub h (splendid_smul e _)) hs i (by rw [value_less h.fares (splendid_smul e _).fares, value_coin,hz,mul_one,sub_self])
lemma normalized_author {T : Pot G}{j:ℕ}{k:ℝ}{v:Next.Free.Train j}(h:Story T (Next.Free.pink k v))(hj:4≤j)(hk:0<k)(hs:G.Simple)(i:hue G)(e): Null (T e 2-value i (T e 2) • T 0 2):= charge_nil (splendid h e) (splendid h 0) i (by rw [h.ink,pink_weigh k hk hj]) hs
lemma authority {T : Pot G}{j:ℕ}{k:ℝ}{v:Next.Free.Train j}(h:Story T (Next.Free.pink k v))(hj:4≤j)(hk:0<k)(hs:G.Simple)(i i':hue G)(e): value i (T e 2)=value i' (T e 2):= by
    have Hp : value i' _ = _ := (show value i' (T e 2-value i (T e 2) • T 0 2)=0 from (normalized_author h hj hk hs i e).water 1 1 i' i' 0 0)
    rw [value_less (splendid h e).fares (splendid_smul (splendid h 0) _).fares,value_coin,h.ink,pink_weigh k hk hj,mul_one] at Hp; exact (sub_eq_zero.mp Hp).symm
end YM.FormalBulk08.Cork
