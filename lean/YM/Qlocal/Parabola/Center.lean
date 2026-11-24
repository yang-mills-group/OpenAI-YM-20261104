import YM.Qlocal.Parabola.Notebook
import YM.Qlocal.Discount
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Bank Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
open Publishing Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories RG3.Forms Emissions
variable {G:Gauge}{n:Side}{w t v c d b δ κ b' v':ℝ}{k:ℕ}{V Ω ι:Type}[DecidableEq V]{R:Census V}
    {A:Activities G n} {P:BudgetPoint}{s:V→Support n}{o:V→Site n} {Z:Support n}
    {Lp:ι→Ray R}{U:ι→Support n}{q:Ray R}
open Merge Switch
lemma conventional_p (s:Spirit q)(u:V→ℝ)(hu:∀ i,0<u i): Rental (rent u q):= by
 refine ⟨rent_spend hu s.fresh,fun a b c h=>?_,by rw [rent,exchange, Poly.quiet_toll,s.light]; simp⟩
 let w j:=if (j:Bool) then a else b; have hx : ({true,false}:Finset Bool).biUnion (fun i=>(w i).val)=c.val:= by unfold w; simpa using h.2
 have hh : Fits w {true,false}:= ?_; swap
 · refine ⟨fun i hi j hj ih=> ?_,?_⟩
   · cases i <;> cases j <;> simp [Function.onFun,w,h.1,h.1.symm] at *
   rw [hx]; exact c.prop
 have he: unionTag w {true,false} hh=c:= Subtype.ext hx
 have hz:= health 1 s le_rfl hu w {true,false} hh; rw [he,show Emissions.shift 1 u=u from (by ext i; simp [Emissions.shift])] at hz; simpa [w] using hz
variable {J J':Type}{r : RG.Rep G n}
variable [Countable J][Nonempty V][Countable J'][Fintype V]
    (L:Ledger Ω J G n R) (Y:Ledger Ω J' G n R)(hp:L.forced=Y.forced)
    (h:Ethics r o s L) (h0:Bulk r s L q (t+δ) v b')
    (h':Ethics r o s Y)(he': Bulk r s Y q (t+δ) c b')
    (C : Bank r.activities r.p.threshold)
    (S: Corrections G n)
    (K:Ω → ℕ→ Config G n→Poly R)
    (hx:∀ x,Changes r.p S (markRead (r:=r) L x) (markRead (r:=r) Y x) (K x) s)
    (p:Rental q) (F:ℕ→ Ray R)(hT:Haze S.region r.p.B (t+δ) F q b)(hv:∀ x i U,CoverP (F i) (K x i U)) (hs:r.activities.ForcedFamily r.p)
    (hd:0≤ δ)(ho:0 ≤ t)(hw:∀ i,(S.region i).Nonempty)
noncomputable def shelter (L:Ledger Ω J G n R): Ledger Ω J G n R:= {L with forced:= fun x=> C.store S r.p (L.forced x) (K x)}
set_option quotPrecheck false
local notation "Γ" => shelter C S K Y
local notation "Y★" => (Γ).taste r o s
local notation "e0"=> (b'+κ⁻¹*(Real.exp (κ*b'+b)-1))
include hp h h0 h' he' hx hT hv hs hd ho hw p
-- Core exact Mark densities. Supports insertion, removal or path.L supported discrepancy when Mark union editor intents paid and aligned at Region. Preserves the FULL marked POLY, including old vacuum.AC.Force Alpha. Output of Mercy.Exec composes. `Ethics Y` on old marks but Y has different raw log; hC reserve part of price. Support replacement requires its own payments.
lemma region (hQ:1≤κ)(hℓ:StellarTree.sites r.p.B * (κ*b'+b) ≤ δ): Ethics r o s Γ ∧ Bulk r s (Γ) q t c e0 ∧ RetainsDeclared (Declared r s R) Y★ s ∧ Peak r o Y★ q t c e0 ∧ ∀ x, ((L.taste r o s).leaf x).density=((Y★).leaf x).density:= by
 obtain ⟨g,hg,hY⟩:= tab Y p he'; let hm:= preserved C p hg hT hs (regard Y h') hx hY hv hw hℓ ho hQ hd; let f:=Γ
 have hK(x): Authority r.p r.activities s (f.forced x):= (hm.1 x).2
 have hE:= reshaped Y h' f.forced hK; have he: Bulk r s f q t c e0:= trims Y p he' hd hK hm.2.1 (fun i x=>hm.2.2 x i)
 refine ⟨hE,he, Publishing.retains_ hE, Publishing.assemble hE q (fun v=>(p.pos v).le) he,fun x=>?_⟩
 ext1 U; rw [published L h p (add_nonneg ho hd) h0,published f hE p ho he]; rw [hp]; exact congr_arg ((Real.exp (r.exponent U):ℂ) • ·) (congr_fun (hm.1 x).1 U)
end YM.Qlocal.Parabola
