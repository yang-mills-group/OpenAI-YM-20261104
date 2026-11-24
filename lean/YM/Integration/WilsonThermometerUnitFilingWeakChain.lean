import YM.Integration.WilsonThermometerUnitFilingWeakStep

/-! Absolute convergence of the neutral angular history on the selected Wilson course. At each visit retain the original lifted displacement and the child sector. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakChain
open Function Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08 FormalBulk08 Flat Stationary
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingWeakRibbon
open scoped Classical BigOperators
variable {G:Gauge} {I U E:Type} [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SiteList (U:Type)(r:ℕ) where
  origin : Cover
  sites : Fin r → Cover
  face : Fin r → U

def child {r:ℕ}(L:Side)(a:SiteList U r)(z:Fin r → Cover × U):SiteList U r :=
  ⟨rent L a.origin,fun h=>rent L (a.sites h)+(z h).1,fun h=>(z h).2⟩

def rentAt {r:ℕ}(s:ℝ)(a:SiteList U r):ℝ:=old s r a.origin a.sites

def term {r:ℕ}(L:Side)(K:Bloch.Row I U)(tag:Fin r→ I)(a:SiteList U r)
    (f:SiteList U r→E)(z:Fin r→ Cover × U):E:=
  (∏h:Fin r,K (tag h) (z h).2 (z h).1) • f (child L a z)

theorem row {r:ℕ}(L:Side)(K:Bloch.Row I U)(tag:Fin r→ I)(a:SiteList U r){s w:ℝ}
    (h:∀box:Fin r→Finset Cover,after L s K a.origin a.sites tag box ≤ rentAt w a)
    (f:SiteList U r→E)(paid:∀x,‖f x‖ ≤ rentAt s x):
    Summable (fun z=>‖term L K tag a f z‖) ∧
      ‖∑' z,term L K tag a f z‖ ≤ rentAt w a:=by
  have quote (T:Finset (Fin r→ Cover × U)): ∑z∈T,‖term L K tag a f z‖ ≤ rentAt w a:=by
    let box (i:Fin r):Finset Cover:=T.image (fun z=>(z i).1)
    let window:=Fintype.piFinset (fun j=>(box j) ×ˢ (univ:Finset U))
    have ins:T ⊆ window:=by
      intro z hz
      apply Fintype.mem_piFinset.mpr
      intro j
      exact mem_product.mpr ⟨mem_image.mpr ⟨z,hz,rfl⟩,mem_univ _⟩
    refine (sum_le_sum_of_subset_of_nonneg ins (fun z _ _=>norm_nonneg (term L K tag a f z))).trans ?_
    apply LE.le.trans _ (h box)
    apply sum_le_sum
    intro z _
    calc
      _ = (∏j:Fin r,‖K (tag j) (z j).2 (z j).1‖)*‖f (child L a z)‖ :=by rw [term,norm_smul,norm_prod]
      _ ≤ (∏j:Fin r,‖K (tag j) (z j).2 (z j).1‖)*rentAt s (child L a z) :=
        mul_le_mul_of_nonneg_left (paid _) (prod_nonneg fun _ _=>norm_nonneg _)
      _ = _ :=by rw [mul_comm];simp only [rentAt,old,child,shifted,prod_mul_distrib]
  have sm:=summable_of_sum_le (fun z=>norm_nonneg (term L K tag a f z)) quote
  exact ⟨sm,(norm_tsum_le_tsum_norm sm).trans (sm.tsum_le_of_sum_le quote)⟩

def face (c:Bool):Type:=TypeFace (if c then 1 else 2)

instance (c:Bool):Fintype (face c):=by unfold face;infer_instance

def kernel (c:Bool) (K:KernelChoices){j t:ℕ}(P:Flight j t)(l:List Axis):Cross P.L (face c) (face c):=
  match c with
  | true =>advanceC P.L (P.duo K.penalty).A0 l
  | false =>advanceC P.L (P.psi K.penalty) l

def current (R:Run G)(N i:ℕ):=destination R.alloy.B.a N i

def read (R:Run G)(N:ℕ)(c:Bool){r:ℕ}(l:ℕ→List Axis)(i:ℕ)
    (f:SiteList (face c) r→E)(a:SiteList (face c) r):E :=
  let P:=current R N i
  ∑' z,term P.L (kernel c R.metals.p.kernel P (l i))
    (fun j=>(wrap P.L (a.sites j),a.face j)) a f z

def walk {X B:Type*} (edge:ℕ→(X→B)→X→B) (v:ℕ) (f:X→B):ℕ→X→B
| 0=>f
| n+1=>edge (v+n) (walk edge v f n)

theorem original (Q:WilsonOriginalCompoundStrip.Request G)(R:Run G)
    (fund:WilsonOriginalProfileStrip.Filed (WilsonOriginalCompoundStrip.programme
      (WilsonThermometerUnitFilingWeakStrip.enrolled Q)) R.kit)
    (v N H:ℕ)(room:H ≤ R.alloy.B.a.clock.J v)(start:4 ≤ R.alloy.B.a.clock.J v)
    (c:Bool)(l:ℕ→List Axis)(orders:∀i,v ≤ i → i<N → (l i).length ≤ R.alloy.B.a.clock.J (i+1)-2)
    (r:ℕ)(f:SiteList (face c) r→E):
    let ρ:=fun j=>WilsonThermometerUnitFilingWeakStrip.trial Q R.metals.p.kernel (R.alloy.B.a.clock.J j) H
    (∀a,‖f a‖ ≤ rentAt (ρ v) a) → ∀n,v+n ≤ N → ∀a,
        ‖walk (read R N c l) v f n a‖ ≤ rentAt (ρ (v+n)) a:=by
  intro ρ paid n
  induction n with
  | zero => exact fun _ a=>paid a
  | succ n ih =>
    intro hn a
    let i:=v+n
    have low:v ≤ i:=Nat.le_add_right _ _
    have early:i<N:=by dsimp [i];omega
    have m₀:=R.alloy.B.a.fits.mono low
    have m₁:=R.alloy.B.a.fits.mono (Nat.le_succ i)
    let P:=current R N i
    have fund₀:=WilsonThermometerUnitFilingWeakStep.bought Q R fund i H (room.trans m₀)
      (start.trans (m₀.trans m₁)) (start.trans m₀) (R.alloy.B.a.fits.stepSlow i) (Nat.le_succ _)
      P (WilsonThermometerUnitFilingWeakStep.block R N i) (l i) (orders i low early) r a.origin a.sites
    have h:∀box:Fin r→Finset Cover,after P.L (ρ i) (kernel c R.metals.p.kernel P (l i)) a.origin a.sites
        (fun j=>(wrap P.L (a.sites j),a.face j)) box ≤ rentAt (ρ (i+1)) a:=by
      cases c with
      | true => exact fund₀.1 _
      | false => exact fund₀.2 _
    exact (row P.L _ _ a h _ (ih (by omega))).2

end YM.Integration.WilsonThermometerUnitFilingWeakChain
