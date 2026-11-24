import YM.RG12.Joint.Pivot
import YM.UVExtension.Oasis.Hall
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast.RG12Joint
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

-- reveal retained PPX
include R
lemma direction (hn:m<N)(he:d+3≤ (T).clock.J m): let C':= C ((T).clock.J (m+1)); let L:=(T).S.block m; ∃ k: Heading F,(let f:=((T).budget (m+1)).threshold; let c:=((T).budget m).threshold; ∀ i j:(F).Index,((F).grades i).1≤((F).grades j).1 → k.map (Planned.PrimaryIntegral295.Place.copy F j) i=if i=j then (((c/f:ℝ):ℂ))^((F).grades i).2 else 0)∧ (∀ u, (F).coeffSize (k.map u) ≤ C' * (F).coeffSize u ∧ (F).coeffSize (k.map.symm u) ≤ C' * (F).coeffSize u) ∧ (∃ o:ℝ, Push.Local.Leading (k.map.toLinearMap) o) ∧ Tips (Z) L k (Doors.rate L) C':=by
   intro c L; let K:=(ray S N n m z! hn).body
   have hv:=(housed S v); let i:=A.B.a.clock.J m; let j:= A.B.a.clock.J (m+1); have hx:=step_paid A.B.a m; have hh:d ≤ i:=le_trans (Nat.le_add_right d 3) he
   have hC: Buys H F W m c (Doors.rate ((T).S.block m)):= R.clock.fits H rfl m d hh
   have hN: Waged K beam0 (readC S R d N m n z! he) (slots1 S N m n z! hn) (Planned.GuardedAtom.Guard.Keeper.sufficient (slots0 S N m n z! hn)) Z:= follows S R _ _ _ _ _ hn he -- d N m
   dsimp only [L]; rw [Push.PriceCompiler.block_eq A.B.valid]
   exact Cub.RG12Joint.ppx_tip hn R.songs R.PStage R.wait (Graces.feet he R.clock) hv R.r K beam0 (ponds S N n m z! hn) rfl hG R.tunes R.corners R.shape R.clock R.stamp (readC S R d N m n z! he) (slots1 S N m n z! hn) _ hN he (zero_le_one.trans hC.cost)
-- floor for orbit multiplication in sailC
structure Board (M:Metals G)(P:Rolls M.p) : Prop where
   wood (d j:ℕ)(hi:d ≤ j): let r:= P.L j; let s:=(M.p.profile j).columns
     (Doors.rate r + 2*Doors.rate r * s)*orbitCost ((frames G).level d) ≤ Bid.barunit r

section
variable (s: Sheet G) (T0:MapPrices)
omit R in
lemma extra_board: ∃ n:ℕ→ℕ,∀ v:ℕ→ℕ,n≤v→ ∀ P:Rolls (UVExtension.Case.provider s T0 v).p, Board (UVExtension.Case.provider s T0 v) P:=by
   choose k hk using fun j d : ℕ => Doors.pre_tilt (2*(s.profile j).columns) (orbitCost ((frames G).level d))
   refine ⟨fun i=> (Finset.range (i+1)).sup (k i),fun v he P=>⟨fun d j hj=>?_⟩⟩
   let r:=P.L j; have hu:k j d ≤ r.val:= (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans ((he j).trans (P.large j).need)
   simpa [mul_add,mul_left_comm,mul_assoc,mul_comm,UVExtension.Case.provider,ThroughLaunch.raise] using (hk j d r hu).2
end

variable {Bt:Org.Bolt A}(a:Upland.Arc X S Bt)(t:ℕ→ℕ)(hk:Lisle t A.B.a)
local notation "U"=> cellar S R a t hk
local notation "nB"=> A.B.a.S.side m n
-- mast sailing estimate on these exact coordinates
include a hk
lemma stacking (h:Board M P) (d N n m:ℕ)(hm:t d ≤ m)(hn:m<N): let p:=Cellar.gate v (cellar S R a t hk) d N n; Triangle H W m (fun x=> (p.entries (m+1) x).x) (fun x=> (p.entries m x).x):=by
    intro p; let Y:= (U).cantors v d n; let f:= Y.song N; have hY:= Y.lyr N (hm.trans hn.le)
    have hF(i:ℕ)(hi:t d ≤ i)(hy:i ≤ N)(x): (p.entries i x).x=(f.tone i).index x:=by
      let y:=launch v U d N n; change ((gate ..).entries ..).x= _; rw [gate,(y.choose_spec (hm.trans hn.le)).2]; exact (hY.earned.earned _ hi hy).currents x
    have hm': t d ≤ m+1:=hm.trans (Nat.le_succ _); let i:= A.B.a.clock.J m; let j:= A.B.a.clock.J (m+1); have hz: d+3 ≤ i:= (hk.tops d).trans (A.B.a.fits.mono hm); have hj:d ≤ j:= by have hv:i ≤j:=A.B.a.fits.mono (Nat.le_succ _); omega
    obtain ⟨q,hq,hL,hC,hT⟩:= direction (d:=d) (n:=n) S v R hn hz
    have hb:= R.clock.fits H rfl m d (Nat.le_trans (Nat.le_add_right d 3) hz)
    let s:= (A.B.a.params (m+1)).columns; let L:= (T).S.block m; let c:=C j
    have hs: 0 ≤ s:= zero_le_one.trans (A.B.a.params (m+1)).columns_ge
    have heC : c ≤ W.K j:= (le_mul_of_one_le_right (zero_le_one.trans hb.cost) (orbitCost_one_le ((frames G).level d))).trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (show 0≤ Doors.rate L*s from mul_nonneg (Doors.rate_pos _).le hs)) (zero_le_one.trans (orbitCost_one_le ((frames G).level d)))).trans hb.funds)
    refine ⟨q,hC,fun x=> ⟨((hL _).1.trans ?_),((hL _).2.trans ?_)⟩,fun x=>?_⟩
    rotate_left 2
    · rw [hF _ hm hn.le,hF _ hm' hn]; let g:=fun _:Motion=> tide S R d N m n (v N n); let X0:= fun _:Motion=> hY.Vista (m+1); let nT:=glaring A.B.a m n
      have hi x:= (Lyrics.spaceF hY m hm hn x).1
      change ∀ x, (f.tone m).index x= major g X0 nT ((f.tone (m+1)).index x) at hi
      rw [hi]; apply le_trans (sailC g X0 nT (fun _=> hT) hs (fun i x=> by
        unfold X0; rw [Lyrics.takes hY _ hm' hn]; exact Lyrics.climbs hY _ hm' hn x) _).1
      apply mul_le_mul_of_nonneg_right _ (Work.G08.size_nonneg ..)
      let C' := M.p.profile j; have ht:= h.wood d j hj; dsimp only at ht
      unfold j at ht
      rw [← params_eq A.B.valid (m+1), ← Push.PriceCompiler.block_eq A.B.valid m] at ht; exact ht -- h uses js let
    all_goals exact mul_le_mul_of_nonneg_right heC (Work.G08.size_nonneg ..)
end YM.UVExtension.Mast.RG12Joint
