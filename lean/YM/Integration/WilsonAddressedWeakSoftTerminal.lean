import YM.Integration.WilsonAddressedWeakTerminalPrice
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Denarii
import YM.Next.RANK.Ratchet

/-! Return a compensated full original physical cylinder through the authentic common denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedWeakSoftTerminal
open Function Set Filter RG Source MeasureTheory Wilson Cells Lattice Next.Rank Next.Rank.Ship
open Next.Rank.Glyph Next.Rank.Exponential Next.Rank.Read Next.Rank.Station
open PhysicalNext.InteractingRank.Soft
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {b:ℝ} {n k N p M:ℕ} {x:Points n}

/-- The original finite posted-rep integral proof applies to the very tested cylinder Y. -/
theorem whole (O:HaarBudget G) (hc:Allocated C.path.levels M k O b)
    (hb:bank O C.path.levels (width C.path.levels b k))
    {P:Rep G (C.side (width C.path.levels b k) p)} {u:Course C N p k} {hN:k≤N}
    {q:width C.path.levels b k≤N} (hp:PhysicalNext.InteractingRank.Soft.Ferm P u q)
    (Y:Config G (C.side N p)→veil (Fin n)) (cont:∀s,Continuous fun U=>(Y U).part s)
    (hn:n≤M){e c d:ℝ} (he:0≤e) (hE:c≤1) (hC:d≤1)
    (hv:estimate P u hN x Y e c d (allowance C.path.levels M k))
    (s:modes (Fin n)) (sh:s.val.Nonempty) :
    let T:=yard C b hN p
    T.rootTest (C.beta N p) (fun U=>(Y U).part s) ≤ budget C.path.levels M k := by
  intro T
  let A:= C.path.levels; let r:= width A b k
  obtain ⟨H,σ,g,Λ,δ,w,hD,hd⟩ := hp
  have hea := s_postage (X:=Y) (T:=T) u q O H hd hD.positive hD.entrance hD.assigned rfl (Real.exp_pos _) he cont hv s
  have hc1 := hc.permitted.plateau r le_rfl ((wider A b k).trans (before A b k))
  have hQ : A.params r=A.params k := congr_arg A.clock.stage hc1
  let Z := Fintype.card (Site (A.S.side r p))
  rw [Fintype.card_fin, show Fintype.card T.Cell=Z from rfl] at hea
  have hs : d+n*c ≤ 1+(M:ℝ) := by
    refine add_le_add hC ((mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _ : 0 ≤ (n:ℝ))).trans ?_)
    rw [mul_one]; exact_mod_cast hn
  let I := pot A M k
  have hi : protection O P (A.params r).paths Λ δ (d+n*c) g - 4*G.lieDim*Real.log g/(Z:ℝ) ≤ I := by
    apply (hb p P g Λ δ (d+n*c) M hD hs).trans
    change ticket O (A.params r) M ≤ I; rw [hQ]; exact hc.charge
  apply hea.trans
  let a := allowance A M k
  have ha : 1 ≤ a := fixed ..
  calc
    _ ≤ Real.exp I / a^s.val.card := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hi) (pow_nonneg (zero_le_one.trans ha) _)
    _ ≤ Real.exp I / a := by
      gcongr
      calc
        a = a^1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ ha (Finset.card_pos.mpr sh)
    _ = _ := by change Real.exp I / Real.exp (2*I)=Real.exp (-I); rw [← Real.exp_sub]; congr 1; ring

end YM.Integration.WilsonAddressedWeakSoftTerminal
