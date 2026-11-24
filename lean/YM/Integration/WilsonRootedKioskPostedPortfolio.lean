import YM.Integration.WilsonRootedKioskCompleteFiling

/-! Withdraw the complete filed model before the very same second merger.
Each failed reading remains in its original true enrolled stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskPostedPortfolio
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal
open WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open WilsonRootedKioskWithdrawal (output pass_add)
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I J E:Type}[DecidableEq V][Fintype V][Countable I][Countable J]
  {o:V → Site n}{R:Census V}{e f a c b s d:ℝ}{P:Rep G n}{A:Activities G n}

omit [Countable I] in
theorem quiet (L:Lamps T I G P.p o R)(pure:∀t u,(bare L t u).part R.quiet=0)(F:T → Config G n → Poly R)(t:T)(u:Config G n):
    (output L F t u).part R.quiet=(F t u).part R.quiet:=by
  unfold output
  rw [Poly.quiet_mul, Poly.pass_part _ (by rw [Poly.part_neg,pure,neg_zero]),one_mul]

omit [Countable I] in
theorem incoming (H:Hard T P.p A.forced A.K o R)(L:Lamps T I G P.p o R)
    (Y μ:T → Config G n → Poly R)(enrolled:ReadZone T P.p A H Y μ)(clear:∀t u,(μ t u).part R.quiet=0)(pure:∀t u,(bare L t u).part R.quiet=0):
    ReadZone T P.p A H (output L Y) (fun t u=>-(bare L t u)+μ t u):=by
  intro t u
  obtain ⟨sums,v,eq⟩:=enrolled t u
  have h: (-(bare L t u)).part R.quiet=0:=by rw [Poly.part_neg,pure,neg_zero]
  refine ⟨sums,v,?_⟩
  unfold output
  rw [eq,pass_add _ _ h (clear t u),mul_smul_comm,mul_assoc]

variable (H:Hard T P.p A.forced A.K o R)
variable (D:Kiosk.Second P.p A P.activities e f a c)
variable (L:Lamps T I G P.p o R)(S:Lamps T E G P.p o R)(M:Canopy.ShiftRows T J G P.p o R)

abbrev residual:=Gallery.mk S (Kiosk.Second.canopy H (roll M L) D)

theorem received (w:V → ℝ)(hw:∀v,0<w v)(ha:0≤a)(old:H.Paid w P.p.B (a+1) e)
    (reg:S.Paid w P.p.B a b)(posted:M.Budget w P.p.B (a+1) s)
    (fresh:(sheet L).Budget w P.p.B (a+1) d)(room:s+d≤c)
    (Y μ:T → Config G n → Poly R)(enrolled:ReadZone T P.p A H Y μ)
    (showcase:∀t u,μ t u=L.log t u+S.log t u+M.log t u)
    {w₀:V → ℝ}{a₀ g:ℝ}(h₀:∀v,0<w₀ v)(pa:0≤a₀)(gross:Gross L w₀ P.p.B a₀ g)
    (mu0:∀t u,(μ t u).part R.quiet=0)
    (y0:∀t u,(Y t u).part R.quiet=(P.eval u:ℂ))(positive:∀u,P.eval u≠0):
    let O:=residual H D L S M
    O.Pays w a b f ∧ (∀t,output L Y t=O.density t) ∧
    ∀t u,(O.density t u).part R.quiet=(P.eval u:ℂ):=by
  have pure:=WilsonRootedKioskCompleteFiling.quiet L h₀ pa gross
  have capacity : (roll M L).Budget w P.p.B (a+1) c:=by
    obtain ⟨g,cover,hit⟩:=(stack M L posted fresh).earned
    exact ⟨g,cover,fun x=>budget_loosen (hit x) room⟩
  have more:0≤a+1:=by linarith
  have remaining (t) (u):-(bare L t u)+μ t u=S.log t u+(roll M L).log t u:=by
    rw [showcase,WilsonRootedKioskCompleteFiling.split L h₀ pa gross,ordered M L t u (M.earnings posted hw more t u) ((sheet L).earnings fresh hw more t u)]
    abel
  have transcript:=incoming H L Y μ enrolled mu0 pure
  obtain ⟨paid,done⟩:=Kiosk.Second.passes (output L Y) (fun t u=>-(bare L t u)+μ t u) H (roll M L) D hw ha old capacity transcript S.log remaining
    (fun t u=>Lamps.quiet_of_hasSum t u (reg.sums ha hw t u))
  have actual (t) (u):(output L Y t u).part R.quiet=(P.eval u:ℂ):=(quiet L pure Y t u).trans (y0 t u)
  have whole:=upkeep (output L Y) P S (Kiosk.Second.canopy H (roll M L) D) reg ha hw done actual positive
  exact ⟨⟨reg,paid⟩,whole,fun t u=>(congrArg (fun z:Config G n → Poly R=>(z u).part R.quiet) (whole t).symm).trans (actual t u)⟩
end YM.Integration.WilsonRootedKioskPostedPortfolio
