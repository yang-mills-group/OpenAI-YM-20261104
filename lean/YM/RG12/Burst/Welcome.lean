import YM.RG12.Burst.Home
import YM.RG12.Shadows.Public
import YM.RG12.Burst.Dindon
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast.RG12Burst
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Bid Motion Cellar
variable {G : Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) (v:Keys S) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    {d N m n:ℕ}
set_option quotPrecheck false
local notation "H"=> Orchard.Path S v
local notation "T"=> A.B.a
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "z!"=> v N n
local notation "Z"=> tide S R d N m n (v N n)

open Planned.GuardedAtom Guard Pressure ConnectedActivityE6 Greenbelt
open Daisy.Charity.RG12 Blush.Burst10
variable (ζ : Mallow.RG12.Earned (garment11 G) X.shape A.delay) (hm:m<N)(hh:d+3 ≤ A.B.a.clock.J m)
local notation "B'" => (ray S N n m (z!) hm).body
local notation "Γ" => beam0
local notation "Γ0" => houseS B' Γ
local notation "Ω" => badge G (A.B.a.S.side (m+1) n) d
local notation "U!" => slots1 S N m n (z!) hm
local notation "h!" => Keeper.sufficient (slots0 S N m n (z!) hm)
local notation "R!" => readC S R d N m n (z!) hh
local notation "InP"=>S.realBeat (0:ℝ) N n (m+1) -- z! is Route? v not zero!
local notation "v'"=> ((P.L (A.B.a.clock.J (m+1))).val : ℂ)^d
-- Need determine actual rep: z!=v N n.RΞ.J readC lean print
include ζ hm hh
set_option maxHeartbeats 650000 in
lemma menu11 (i: ((Labels.frames G).level d).Index) -- using inferred M and payer from inputs
    (hi:i≠0) :
    let K:=lark _ i R! U!; let k0:= ((A.B.a).budget m); let J0:= (Z).vane (some i)
    let L':= Blush.Burst10.lots (B:=k0) Γ0 K 0 v' ((Labels.frames G).level d) (hol G) Ω
    Summable (tendrils (B:=k0) Γ0 K 0 v' ((Labels.frames G).level d) (hol G) Ω)∧
    (∀ p:(Γ0).fragrances, ¬ Duo Γ0 K p → tendrils (B:=k0) Γ0 K 0 v' ((Labels.frames G).level d) (hol G) Ω p=0)∧
    ((Labels.frames G).level d).coeffSize ((J0.1-Push.Local.weighted (hol G) ((Labels.frames G).level d) 0 (Brim.plate Γ0 Ω).support k0.threshold (Blush.pane Γ0 K v' (Brim.icon Γ0 Ω))) - L') ≤ A.B.a.clock.hatBeta (m+1)^(-(4/5):ℝ)*MergeProof.load K.live :=by
      intro K P' J L'
      have he:=follows S R d N m n (z!) hm hh
      obtain ⟨h0,h1⟩:= fair11 (d:=d) hm (B') (Γ) R.clock h! K ζ (le_trans (Nat.le_add_right ..) hh) ((skin ..).symm ▸ (ankle : 0∈ ((localSection G d).footprint (0:Site _))))
      obtain ⟨hp0,hp1,hp'⟩:= duplex _ _ _ _ _ _ h0 (k:=Ω) (show K.live.turn=.logKey Ω from rfl)
      refine ⟨hp1,hp',?_⟩
      unfold J; rw [he.pace i hi]; rw [hp0] at h1
      rw [sub_sub]; exact h1

section
variable (k:StockTag (A.B.a.S.side (m+1) n))
local notation "B₀"=> (S.realBeat (z!|>.val) N n (m+1)|>.p)
local notation "Rt" => S.realBeat (z!|>.val) N n (m+1)
local notation "Π"=> Eyelet.fee B₀ k.val.1
local notation "Δ"=>Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "n1"=> (A.B.a.S.side (m+1) n)
-- normalize input wing before estimating op norm on entire cast.
set_option maxHeartbeats 880000 in
theorem wing11 (p: Stream G (B₀) k) : (F).coeffSize ((Z).wing k p).1 ≤ A.B.a.clock.hatBeta (m+1)^(-(4/5):ℝ) *Δ* ‖p‖ :=by
   have he:=follows S R d N m n (z!) hm hh
   have hzθ : 0< A.B.a.clock.hatBeta (m+1):= zero_lt_one.trans (T|>.fits.delayed _)
   set c:= A.B.a.clock.hatBeta (m+1)^(-(4/5):ℝ)
   have hc:0<c:= Real.rpow_pos_of_pos hzθ _; have hPi : 0< Π:= Eyelet.toll_pos ..
   have hDelta:= glyphBound (T) (m+1)
   by_cases h: (0:Site n1)∈ k.val.1
   swap; · rw [he.blank _ h]; change (F).coeffSize 0 ≤ c * Δ * ‖p‖; simpa [Frame.coeffSize] using! (show 0 ≤ c*Δ*‖p‖ by positivity)
   let hr:=he.limb k h; let V: ℝ:=Π/Δ; have hV:0<V:=div_pos hPi hDelta.1
   let L0:= twig (sink (G:=G) (B₀) k); have hh':DenseRange L0:= steams _
   refine hh'.induction_on (p:=fun p=> (F).coeffSize ((Z).wing k p).1 ≤ A.B.a.clock.hatBeta (m+1)^(-(4/5):ℝ) * Δ * ‖p‖) p (isClosed_le (f:=fun p:Stream G (B₀) k=> (F).coeffSize ((Z).wing k p).1) (show Continuous _ from (show Continuous ((F).coeffSize) by unfold Frame.coeffSize; fun_prop).comp ((Z).wing k).continuous.fst) (continuous_const.mul continuous_norm)) ?_
   intro p
   let a:= ‖L0 p‖; have ha:∀ U, ‖p.val U‖≤a:= (debts B₀ k p).2 (le_refl _); let M':=vaneT (Q:=fun _=> Rt) (A:=A) (n:=n) (m:=m) (Γ) U! k p a ha
   have hx:M'.live.crest=k.val.1:= congr_arg Prod.fst (cardK (R:=Rt) _ _)
   have hv:= (fair11 (d:=d) hm (B') (Γ) R.clock h! M' ζ (le_trans (Nat.le_add_right ..) hh) (hx.symm ▸ h : 0∈ M'.live.crest)).2
   rw [gasEra (Γ0) M' 0 v' F _ (show M'.live.turn=.gasKey (cart (R:=Rt) (Keeper.sufficient U!) k) from rfl),sub_zero] at hv
   let Q:=Z; let x :=Q.wing k (L0 p); let e:=((frames G).level d).coeffSize x.1
   have he: tars (B') Γ (h!) M' d = (V:ℂ) • x:= by rw [hr.linke _ _ ha,map_smul]; rfl
   have heq : (F).coeffSize (((V:ℂ) • x).1)=V*e:=by erw [Size.smul (F) (V:ℂ) x.1,Complex.norm_real _, Real.norm_of_nonneg hV.le]
   rw [he,heq] at hv
   change e≤ c * Δ * a; have hu : (Rt).p.mass M'.live.crest M'.live.weight = Π*a:=by rw [hx]; rfl
   change V*e ≤ c*((Rt).p.mass _ _) at hv; rw [hu,show Π*a= V*(Δ*a) from ?_,← mul_left_comm] at hv
   · exact (le_of_mul_le_mul_left hv hV).trans_eq (mul_assoc ..).symm
   unfold V; field_simp [hDelta.1.ne']
end
end YM.UVExtension.Mast.RG12Burst
