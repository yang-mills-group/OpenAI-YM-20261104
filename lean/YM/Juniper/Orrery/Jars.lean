import YM.Juniper.Orrery.Parasol
/-!
 # Lift the budgeted roster of the Canister (also into THE GIVEN full
 Charm/Pylon, not just primary). Doesn't ask annulus estimates separate
 at all aligned periods or low E model on all op outputs. Membership uses cut.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Org Pane Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost Guild Tabernacle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (R:Factor A) {c C f F:Side}{N m n k:ℕ}(hm:m<N)
   {θ χ:ℝ}
local notation "L"=> A.B.a.clock
local notation "Z"=> (L).hatBeta m
local notation "W"=> (L).hatBeta (m+1)
local notation "U"=> (A.B.a.budget m)
local notation "B"=> (A.B.a.budget (m+1))
local notation "φ"=> (A.B.kin.path N (m+1))
local notation "P"=> (A.B.a.params (m+1))
local notation "L*"=> A.B.a.S.block m
local notation "Λ"=> (L).allowance (m+1)
local notation "δ"=> (L).forcedAllowance (m+1)
local notation "J"=> (L).J (m+1)
local notation "I"=> (L).J m
variable (T : Canister G (A.B.a.budget (m+1)) (A.B.a.clock.allowance (m+1)) χ) (s:f.val=c.val*(A.B.a.S.block m).val)
   (S:F.val=C.val*(A.B.a.S.block m).val)
noncomputable def auxiliary (θ:ℝ) : RG.Rep G f := { Pane.virgin (orchestra A N s) B θ with activities:=pod B (T.prior f) }
abbrev Loft (v:BudgetPoint)(f:Side) := 100*(1+v.B) ≤ f.val
local notation "φ!"=> auxiliary (N:=N) T s θ
local notation "Q"=> (P).clip
local notation "D₀"=> (W)-(Z)
local notation "Ψ"=> (pod B (T.prior f))
variable (h: Tailcoat X.p D A.delay) (hp:θ∈ Rain.lands A m) (hF:Loft (A.B.a.budget m) c)
local notation "H"=> Pane.panel A m s
local notation "W'"=> Pane.orchestra A N s
local notation "Ω"=> ((H).ratio)
include h hF s -- hF c actual n signature beware
lemma wideJ : Margin B f:= by
    have he:= Orrery.coversR h (m:=m); have hx:= Nat.le_mul_of_pos_right c.val (show 0<(A.B.a.S.block m).val from (A.B.a.S.block m).pos); unfold Loft at hF; unfold Margin; omega
include hp hm R
lemma temple : ∃ g:Chartlet R.shape A N m s (auxiliary (N:=N) T s θ), SeekR R.shape A N m s g:= by
    have hu:= Pane.ingots A N s hm hF hp; have hx:= (Canister.earns T _ (Orrery.wideJ s h hF)); have hP := (Orrery.frames _ T (Orrery.wideJ s h hF)); let U₁:=φ!; let a:= A.B.a; let f:=(T.prior f).field
    refine ((R.shape.consumes J I (PriceCompiler.step_paid A.B.a m)).2.2.2 Z ((R.pledging.conducts.income.grow.1 J).trans (A.B.valid.pays m))).2 _ _ _ W' (Pane.accepts A N s hm hF)|>.2 (Pane.ovation A N s hm R.pledging.conducts.full) U₁ ?_
    let K':= Pane.virgin W' B θ; refine ⟨hu.ready,⟨rfl,rfl,hu.received.temp⟩,⟨hu.cap.paths,?_⟩, hu.exponent,hu.height,hu.sizes,hu.window⟩
    have he := (ConnectedActivityE6.Application.clock_next a m 0); have he : W=betaF G Z (H).patch.L:=he
    refine ⟨hP.regular,hP.forced,hP.moves,?_,Time.K_rises hP.boundK (Real.exp_pos _).le⟩; unfold incomingE; rw [← he]; exact hP.boundE
omit hp hm R
section tuning
variable {u₀ : RG.Rep G f} (K:Carved (pod (A.B.a.budget (m+1)) (T.prior f)).reg (pod (A.B.a.budget (m+1)) (T.prior f)).E u₀.activities.reg u₀.activities.E)
-- build Tape without assuming post generation at this step
include s
noncomputable def event : tapeFor R s u₀ where
    names j:= (T.windows f j).map K.θ
    halls j i hI:=by
       obtain ⟨i,hi,rfl⟩:= mem_map.mp hI; apply Orrery.telescope Ω ((U).B) _ u₀ (U).B_pos (Orrery.coversR h (m:=m)); rw [K.align]; exact T.access f (wideJ s h hF) _ _ hi
    covers i hi:= by
       obtain ⟨V,hV⟩:= hi; have he : u₀.activities.E i≠0:=by
          rintro hx; unfold Activities.regularOccurrence at hV; rw [hx] at hV; simp [masked, Set.indicator] at hV
       obtain ⟨i,rfl⟩:= show i∈Set.range K.θ from Classical.byContradiction fun hx=> he (K.forget i hx)
       exact (T.active f (wideJ s h hF) _ fun ht=> he ((K.keeps i).trans ht)).mono (fun i hk=> mem_map_of_mem _ hk)
local notation "e"=> event R T s h hF K
local notation "v₀"=> auxiliary T S θ (N:=N)
local notation "K₁"=> Carved.refl (pod (A.B.a.budget (m+1)) (T.prior F)).reg (pod (A.B.a.budget (m+1)) (T.prior F)).E
local notation "P'"=> Pane.panel A m S
-- project Volume from dense reference tape all covers to THIS lifting
variable (hh:C.val=c.val*k) (hT:Loft (A.B.a.budget m) C)
local notation "v'"=> event (u₀:= v₀) R T S h hT K₁
include K
include R
lemma volumeP {he:2≤c.val}(j:ℕ): Nonempty (Flare.Volume (Lace.project («P»:=(H).patch) (h:=s) («H»:=S) (M:=k) hh he) v' e j) := by -- notation clash v' uses e
    let f':=v₀; let S':=(P'); let a':= Lace.project («P»:=(H).patch) (h:=s) («H»:=S) (M:=k) hh he; let x:= a'.low.cut; let y:= a'.high.cut
    -- High side F inferred since u defined
    have h₀:F.val=f.val*k:=by rw [s,S,hh]; ac_rfl
    obtain ⟨p,hp⟩:= T.projects f F k h₀ (wideJ s h hF) j
    let a i:=K.θ (p i); have h₁ : (v'|>.names j)= T.windows F j:= by ext i; change i∈ (T.windows F j).map (Embedding.refl _) ↔ _; rw [Finset.map_refl]
    have hL (i) (hi:i∈(v').names j) : i∈T.windows F j := show i∈T.windows F j from h₁ ▸ hi
    have he'(i:ℕ)(U':Config G f)(hi:i∈T.windows F j): f'.activities.E i (a'.high.links U')= (φ!).activities.E (p i) U':=by -- replace
        change (pod B (T.prior F)|>.E i ((Macrame.normal (Deck.divides h₀) h₀).links U'))=(pod B (T.prior f)|>.E (p i) U'); simp only [pod, prune, Orrery.pris]; rw [if_pos (T.access F (wideJ S h hT) _ i hi), if_pos (T.access f (wideJ s h hF) _ (p i) (hp.root i hi|>.1))]; exact hp.truer i hi U'
    refine ⟨⟨a,fun i hi=> ?_, fun i u h₁' hb=>?_,fun i u hi hx he hE=> ?_⟩⟩
    · have hh' := hp.root i (hL i hi); refine ⟨mem_map_of_mem K.θ hh'.1,?_⟩; refine ⟨?_,?_,?_⟩
      · unfold a Flare.fanchor; rw [K.align]; exact hh'.2
      · unfold a; rw [K.align]; exact hp.stable i (hL i hi)
      intro V h; unfold a; rw [K.keeps]; exact he' i V (hL i hi)
    · obtain ⟨i,hi,rfl⟩:= mem_map.mp h₁'; unfold Flare.fanchor at hb; rw [K.align] at hb
      obtain ⟨z,hq,hz⟩:= (Deck.footing («P»:=(H).patch) (h:=s) («H»:=S) hh he).extend u ((pod B (T.prior f)|>.reg i).site) hb; obtain ⟨i',hi',hp,hp'⟩:= hp.serves i z hi hq; exact ⟨i',h₁ ▸ hi', congr_arg K.θ hp, (congr_arg (decreed S).parent hp').trans hz⟩ -- hp lemma NatCast congr
    · have ht:= K.θ.injective he; have he' := (hp.root i (hL i hi)).2; refine hp.uniqueness i u (hL i hi) (hL u hx) ((Deck.footing («P»:=(H).patch) (h:=s) («H»:=S) hh ?_).firm _ _ ?_ hE).symm ht
      · unfold Loft at hF; omega
      exact he'.trans ((ht ▸ hp.root u (hL u hx)|>.2).symm) -- parentheses
end tuning
end YM.Juniper.Orrery
