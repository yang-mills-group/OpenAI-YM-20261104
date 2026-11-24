import YM.FormalBulk08.Castor.Atlas
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Castor
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K: KernelChoices}{I X:Type}{D E l u d j t:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}

-- order D just chart probes. reconstruction of any Garden D, measured on Pier; not extension in derivative order outside tested profiles.

def conduct (h:D≤E)(f:Garden E): Garden D:=⟨f.val,(show ContDiff ℝ (E:WithTop ℕ∞) f.val from f.property).of_le (Nat.cast_le.mpr h)⟩
def Coordinated (h:D≤E)(T:Anthem D G)(S:Anthem E G):Prop:= ∀ f:Garden E,T (portrait D (conduct h f))=S (portrait E f)
lemma banner_same[T : Fintype I] {h:D≤E}{A:I→ Anthem D G}{S:I→ Anthem E G}(hP:∀ i,Coordinated h (A i) (S i))(M: Matrix I X Pence): ∀ i,Coordinated h (larch A M i) (larch S M i):=by intro i f; unfold larch; simp only [Finset.sum_apply,Kemp.launch]; simp_rw [show ∀ j, A j (portrait _ _)= _ from fun j=> hP j f]
lemma carry_q {h:D≤E}{T:Anthem D G}{S: Anthem E G}(p:Coordinated h T S)(K:KernelChoices)(Z:Flight j t)(V:Lodge Z.patch)(M:Pot G)(ρ:ChartRatio G)(hp:Z.patch.Branches K G)(hL:2≤Z.L.val)(a:hue G)(d r:ℕ): Coordinated h (migrates a Z V K M ρ hp hL d r T) (migrates a Z V K M ρ hp hL d r S):= by
    intro f; unfold migrates stir; apply congr_arg; unfold quick; apply congr_arg;apply Finset.sum_congr rfl; intro x _; unfold stepsong; rw [through_show,through_show,show bowl x (conduct h f)=conduct h (bowl x f) from rfl,p _]
lemma label_same {X:Roof.Plaza F D}{V:Roof.Plaza F E}{h:D≤E}(he:∀ i, Coordinated h (X i) (V i)):pantry F X=pantry F V:= by ext i j n; change coeff n (echo F (X j) i)=coeff n (echo F (V j) i);rw [echoline,echoline,show (X j) (Pose.inside F i D)= _ from (show _=V j (Pose.inside F i E) from he j (Dawn.tint E _))]
lemma rising (h:D≤E)(k: Seasons)(hp:upper k≤D)(Z:Garden E): notch k hp (portrait D (conduct h Z))=notch k (hp.trans h) (portrait E Z):= by
   let x:=finger hp; let y:Brush E:=⟨Fin.castLE (Nat.add_le_add_right h 1) x.1,x.2⟩; have hy:word y=k:=(draw_any k hp).choose_spec
   rw [notched hp _ x hy,notched _ _ y hy];rfl
variable (F T)
lemma matching (hD:d+1≤ D)(h:D≤ E)(ρ:ChartRatio G)(W:Lab G K X)(a:hue G)(x:X)(i N :ℕ)(j): Coordinated h (bornY ρ W a F T hD x N i j) (bornY ρ W a F T (hD.trans h) x N i j):= by
   unfold bornY Elm.terrace; generalize N-i=t; induction t generalizing i j with
   | zero=> rw [walkF,walkF]; intro p; unfold sectionY; rw [rising]
   | succ n ih=>
     rw [walkF,walkF];let t:=W.wood x i
     let k(v:ℕ)(hd:d+1≤v):=migrates a (stageHop (W.V x) i (flying (W.V x) n (i+1))) t K (Dove.voyage (W.V x) (W.wood x) (W.toEmpire.bill x) ρ a n (i+1)) ρ (W.toEmpire.bill x i) (growL _ _) d d ∘Elm.walkF ρ (W.V x) (W.wood x) (W.toEmpire.bill x) a F T hd n (i+1)
     let V:=k D hD; let Y:=k E (hD.trans h); have hk j:Coordinated h (V j) (Y j):= carry_q (ih (i+1) j) K _ _ _ _ _ _ _ _ _
     change Coordinated h (larch V (pantry F V)⁻¹ j) (larch Y (pantry F Y)⁻¹ j); rw [label_same hk];exact banner_same hk _ j
lemma dress (hD:d+1≤ D)(h:D≤ E)(ρ:ChartRatio G)(W:Lab G K X)(a:hue G)(x:X)(i:ℕ)(j): Coordinated h (issue W ρ a F T hD x i j) (issue W ρ a F T (hD.trans h) x i j):= by intro p; unfold Drift.issue;funext e r; simp_rw [show ∀ n:ℕ,bornY _ _ _ _ _ hD _ n i j (portrait D _) =_ from fun n=> matching F T hD h ρ W a x i n j p]
end YM.FormalBulk08.Castor
