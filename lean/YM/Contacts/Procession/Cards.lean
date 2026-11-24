import YM.Contacts.Procession.Paint
/-!
# PT wheels for actual formal single sources, at all the actor's levels.

Progress. Bids & Guard real density machinery already certified; this is a
PT packet-formation and continuity/expense on that craft. Not assumption
of block-readable real MARK PT comparison. Native, unperturbed Mark frames,
estimates not yet asserted after all steps or addressed shifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Delight
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Tree Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy FreeResolvent Lumen Spark
open Welcome Theater Catch
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{i j m n p:ℕ}
-- don't ever claim L Warm applies across arbitrary period schedules. Use shell variable A.
variable (ℒ:Levels G)(M:Horizon ℒ)(E:RackCore ℒ M n)(Q:ChartRatio G)(x:G.ColorIndex)(h:LocalRatio Q){T:MapPrices}(hT:M.Suffices T)
include h hT
-- real Athena.Theater
@[simps! P] def opens (i:ℕ)(hi:i<n): Theater G := ⟨mainFlag ℒ i,ℒ.clock.kernel,M.H n (i+1),M.H n i,Q,h,(M.towers n i).A0,E.heir i hi,E.studio Q x (i+1), T.η (ℒ.clock.J (i+1)),awakened hT hi, (parliament _ h hT E _ hi).blazing⟩
abbrev stage (w:Theater G) (x:G.ColorIndex) := Resetter.sink x (caravan w.Q w.P w.K w.X w.W.V w.next.metric)
-- Rank boost ε.At every level want arbitrary tail widths allowed by pre/post budgets. This lemma only buys some common width + positive powers.Hatched before testing.
lemma issues {e:ℝ≥0}(hi:i<n)(hp:0<e): let Z:= opens ℒ M E Q x h hT i hi; ∃ (σ η:ℝ≥0)(U:TableFee)(a b:ℝ), (η:ℝ)/(Z.L.val:ℝ) ≤ e ∧ Z.Rich σ η a b U := by
   intro Z; have hx := parliament x h hT E _ hi; obtain ⟨hX,hP,σ,η,b,d,u,hh⟩:= Lumen.candles x h hT E hi hx; obtain ⟨hs,ht,hA,hW,hb,hd,hE,hU,hp',T,hF,-⟩:=hh; let s:=min σ e; have hw : 0<s:= lt_min hs hp; have he:s ≤ σ := min_le_left ..; have hPos :1 ≤ (Z.L.val:ℝ):= Nat.one_le_cast.mpr Z.L.property
   have hg:(s:ℝ)/(Z.L.val:ℝ)≤(e:ℝ):= (div_le_self (by positivity) hPos).trans (NNReal.coe_le_coe.mpr (min_le_right ..)); refine ⟨η,s,T,b,1+d,hg,hF,hw, (le_trans (div_le_div_of_nonneg_right (b:=(σ:ℝ)) (by exact_mod_cast he) (?_:_)) hA), strip_mono hW (by exact_mod_cast he) le_rfl, hb, ?_, le_add_of_nonneg_right hE⟩
   · exact (side_pos Z.L).le
   exact strip_mono hd (by exact_mod_cast he) (le_add_of_nonneg_left zero_le_one)
structure Weather (Z:Theater G)(x:G.ColorIndex)(s:ℝ≥0)(U:TableFee) (X:bore G)(p:ℕ)(η:ℝ≥0)(V:TableFee)(y:Dye G) : Prop where
   prices : ∃ σ g u W A B, Z.Rich σ η g u W ∧ (η:ℝ)/Z.L.val≤ s ∧ A=Z.transit p η g u U W ∧ B=Z.lamp p η g u U W ∧ Z.Victory η p X y A B ∧ V=Catch.stool (stage Z x) p A -- capital exposed for views.
   sun : Price (recoil (stage Z x) p (Z.plow p X)) y η V
   land : Mount (recoil (stage Z x) p (Z.plow p X)) p
structure Domain (η:ℝ≥0)(x:Dye G)(U:TableFee)(Z:bore G)(p:ℕ):Prop where
  here : 0<η
  cost : Price Z x η U
  mount : Mount Z p
variable {h hT  M ℒ E x Q}
abbrev turn (Z:Theater G)(x:G.ColorIndex)(Y:bore G)(p:ℕ): bore G:= recoil (Delight.stage Z x) p (Z.plow p Y)
include h hT
lemma bargain (hi:i<n)(Y:bore G)(s:ℝ≥0)(W:TableFee)(y:Dye G)(hw:Domain s y W Y p): let Z:= opens ℒ M E Q x h hT i hi; ∃ η V, Weather Z x s W Y p η V y∧Domain η y V (turn Z x Y p) p:= by
   intro Z; obtain ⟨σ,η,A,a,b,H,hG⟩:= issues ℒ M E Q x h hT hi hw.here; let T:= Z.transit p η a b W A; let w:= Delight.stage Z x; have he:= Z.ecstasy hG hw.mount hw.cost H y; -- implicit Z? def order
   let U:= Catch.stool w p T; have hv: Resetter.Uniform w:= Resetter.sink_mast _ -- x?
   have ht:Price (turn Z x Y p) y η U:=Catch.moving w _ he.up; have hg:Mount (turn Z x Y p) p:=Catch.caring w he.mounted he.up hv; exact ⟨η,U, ⟨⟨σ,a,b,A,T,_,hG,H,rfl,rfl,he,rfl⟩,ht,hg⟩,⟨hG.paid,ht, hg⟩⟩ -- implicit hG binder
-- A walk at arbitrary fixed cutoff, PT all orders before choosing markers
-- no aggregation into a macroscopic test claim here
omit h hT
variable (ℒ M)
variable {M} -- remove syntax toggle?
variable (h hT E x)
def poem (p:ℕ)(X:bore G) (i:ℕ): bore G:= if hx:i<n then Delight.turn (opens ℒ M E Q x h hT i hx) x (poem p X (i+1)) p else X
termination_by n-i
decreasing_by omega
structure Here (Y:bore G)(y:Dye G)(p:ℕ)(b:ℝ≥0)(V:TableFee) (s:ℕ→ℝ≥0)(T':ℕ→TableFee) : Prop where
   starts:s n=b
   birth:T' n=V
   land i (hi:i≤n): Domain (s i) y (T' i) (poem ℒ E x h hT p Y i) p -- shadows h
   all i (hi:i<n): Weather (opens ℒ M E Q x h hT _ hi) x (s (i+1)) (T' (i+1)) (poem ℒ E x h hT p Y (i+1)) p (s i) (T' i) y
include h hT
-- induction choose s,T' from n to 0
private lemma found_shell (i:ℕ)(he:i≤n) (Y:bore G)(s:ℝ≥0)(W:TableFee)(y:Dye G)(p:ℕ)(hw:Domain s y W Y p): let X:= poem ℒ E x h hT p Y; ∃ (ϑ :ℕ→ℝ≥0) (B:ℕ→TableFee), ϑ n=s∧ B n=W ∧ (∀ j:ℕ,i≤ j→j≤ n→Domain (ϑ j) y (B j) (X j) p)∧∀ j:ℕ,i≤ j→∀ h':j<n, Weather (opens ℒ M E Q x h hT j h') x (ϑ (j+1)) (B (j+1)) (X (j+1)) p (ϑ j) (B j) y:= by -- space notation
    intro X; induction he using Nat.decreasingInduction with
    | self =>
        have he:X n=Y:= by unfold X; rw [poem,dif_neg (Nat.lt_irrefl _)]
        exact ⟨fun _=>s,fun _=>W,rfl,rfl,fun j h₁ h₂=>by rw [le_antisymm h₂ h₁,he]; exact hw,fun j h' z=> False.elim (by omega)⟩
    | of_succ i hi ih=>
        obtain ⟨T,B,ht,hB,hH,hs⟩:= ih; let U:= opens ℒ M E Q x h hT i hi; obtain ⟨u,b,hF,hV⟩:= bargain (E:=E) (x:=x) (h:=h) (hT:=hT) hi (X (i+1)) _ _ _ (hH _ le_rfl hi); refine ⟨update T i u,update B i b,?_,?_,?_,?_⟩; · rw [update_of_ne (by omega)]; exact ht
        · rw [update_of_ne (by omega)]; exact hB
        · intro j hj hh; by_cases hz:i=j; · subst j; rw [update_self,update_self,show X i= Delight.turn U x (X (i+1)) p from (by unfold X; rw [poem,dif_pos hi])]; exact hV
          rw [update_of_ne (Ne.symm hz),update_of_ne (Ne.symm hz)]; apply hH j (by omega) hh
        intro j hj hh; rw [update_of_ne (by omega:j+1 ≠ i),update_of_ne (by omega:j+1 ≠ i)]; by_cases hz:i=j; · subst j; rw [update_self, update_self]; exact hF
        rw [update_of_ne (Ne.symm hz),update_of_ne (Ne.symm hz)]; exact hs j (by omega) hh
lemma village (Y:bore G)(s:ℝ≥0)(W:TableFee)(y:Dye G)(p:ℕ)(hw:Domain s y W Y p): ∃ s' W', Here ℒ E x h hT Y y p s W s' W':= by obtain ⟨s',B,hS,hB,hA,hy⟩:= found_shell ℒ E x h hT 0 (by omega) Y s W y p hw; exact ⟨s',B,hS,hB,fun i=> hA i (by omega),fun i=> hy i (by omega)⟩
end YM.Contacts.Procession.Delight
