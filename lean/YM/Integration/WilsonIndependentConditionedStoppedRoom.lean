import YM.Integration.WilsonIndependentConditionedEarlierRoom

/-! The observing stop can precede the public field's home on the same optical collar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedRoom
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open Next.Rank WilsonCoeffUV.Mer.Patrol Extra.Histories
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedActualCredit (badge gramAge homes)
open WilsonIndependentConditionedEarlierCredit (drift)
open WilsonIndependentConditionedProfileCredit (Paid)
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{T U:ℕ}

structure Room (R:Run G)(T U:ℕ) extends WilsonIndependentConditionedEarlierRoom.Room R T U where
  v : ℕ
  stop : |age R v m| ≤ (drift R T U).buy (badge R f)
  reported : |gramAge R v (berth R T f)| ≤ (drift R T U).buy (badge R f)

namespace Room
variable (X:Room R T U)
abbrev K:=X.toRoom.K
abbrev bill:=X.toRoom.bill

theorem cap:1 ≤ X.bill:=X.toRoom.cap

theorem registered {h:WilsonIndependentConditionedEarlierRoom.Room R T U→ℝ}
    (p:Paid WilsonIndependentConditionedEarlierRoom.Room.bill h):
    Paid Room.bill (fun X:Room R T U=>h X.toRoom):=by
  obtain ⟨P,bought⟩:=p
  exact ⟨P,fun X=>bought X.toRoom⟩

theorem ages (R:Run G)(T U:ℕ)(P:Credit):
    Paid (Room.bill (R:=R) (T:=T) (U:=U)) (fun X=>P.buy (age R X.v X.m)) ∧
    Paid Room.bill (fun X:Room R T U=>P.buy (age R X.m X.K)) ∧
    Paid Room.bill (fun X:Room R T U=>P.buy (gramAge R X.v X.K)):=by
  have receive (h:Room R T U→ℝ)
      (s:∀X,|h X| ≤ (drift R T U).buy (badge R X.f)):Paid bill (fun X=>P.buy (h X)):=by
    apply Paid.book _ P
    exact ⟨drift R T U,fun X _=>(s X).trans ((drift R T U).elder X.one X.toRoom.bound.1)⟩
  exact ⟨receive _ Room.stop,registered (WilsonIndependentConditionedEarlierRoom.Room.ages R T U P).2.1,
    receive _ Room.reported⟩

theorem homeAge (R:Run G)(T U:ℕ)(P:Credit):
    Paid bill (fun X:Room R T U=>P.buy (age R X.m X.m)):=
  registered (WilsonIndependentConditionedEarlierRoom.Room.ages R T U P).1

theorem shapes:
    Paid (bill (R:=R) (T:=T) (U:=U)) (fun X=>X.t⁻¹) ∧
    Paid bill (fun X:Room R T U=>X.z) ∧ ∀s:Fin 2,Paid bill (fun X:Room R T U=>X.B s):=by
  obtain ⟨t,z,B⟩:=WilsonIndependentConditionedEarlierRoom.Room.shapes (R:=R) (T:=T) (U:=U)
  exact ⟨registered t,registered z,fun s=>registered (B s)⟩
end Room

theorem reach (R:Run G)(simple:G.Simple){first v m f K U:ℕ}
    (before:first ≤ v)(home:v ≤ m)(mf:m ≤ f)(fk:f ≤ K)(warm:1 ≤ badge R f)
    (optical:R.family.S.scale K-R.family.S.scale first ≤
      (U:ℝ)*(1+badge R v)):
    R.family.S.a v/R.family.S.a f ≤ (R.family.path.levels.clock.hatBeta f)^(2*U):=by
  let A:=R.family.path.levels
  have vp:0<R.family.S.a v:=R.family.S.a_pos _
  have fp:0<R.family.S.a f:=R.family.S.a_pos _
  have hp:0<A.clock.hatBeta f:=zero_lt_one.trans (A.fits.delayed f)
  have bh:badge R v ≤ badge R f:=log_le_log (zero_lt_one.trans (A.fits.delayed v))
    (WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le (home.trans mf))
  have delta:R.family.S.scale f-R.family.S.scale v ≤ R.family.S.scale K-R.family.S.scale first:=
    sub_le_sub ((OPE.scale_mono R.family.S).monotone fk) ((OPE.scale_mono R.family.S).monotone before)
  have bill:R.family.S.scale f-R.family.S.scale v ≤ ((2*U:ℕ):ℝ)*badge R f:=by
    push_cast
    have upper:=mul_le_mul_of_nonneg_left (add_le_add warm bh) (Nat.cast_nonneg U (α:=ℝ))
    linarith only [delta.trans optical,upper]
  apply (log_le_log_iff (div_pos vp fp) (pow_pos hp (2*U))).mp
  rw [log_div vp.ne' fp.ne',log_pow]
  simpa only [Schedule.scale,log_inv,neg_sub_neg,badge,A] using bill

theorem appoint (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(T U:ℕ):
    ∀ᶠ f:ℕ in atTop,∀{first v m:ℕ},first ≤ v → v ≤ m → m ≤ f →
      let K:=berth R T f
      R.family.S.scale K-R.family.S.scale first ≤ (U:ℝ)*(1+badge R v) →
      ∀(t z:ℝ)(B:Fin 2→ℝ),∃X:Room R T (2*U),X.f=f ∧ X.m=m ∧ X.v=v ∧
        X.t=t ∧ X.z=z ∧ X.B=B:=by
  have late:∀ᶠ f:ℕ in atTop,1 ≤ badge R f:=(tendsto_log_atTop.comp
    (Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1
  filter_upwards [late,WilsonIndependentConditionedEarlierCredit.original R simple slow T (2*U),
    WilsonAddressedCollarWindow.original R simple slow T (η:=1) zero_lt_one] with f warm buy gap
  intro first v m firstv vm mf K span t z B
  have old:=reach R simple firstv vm mf gap.1.le warm span
  have am:R.family.S.a m ≤ R.family.S.a v:=by
    apply (log_le_log_iff (R.family.S.a_pos m) (R.family.S.a_pos v)).mp
    simpa only [Schedule.scale,log_inv,neg_le_neg_iff] using (OPE.scale_mono R.family.S).monotone vm
  have msmall:R.family.S.a m/R.family.S.a f ≤ (R.family.path.levels.clock.hatBeta f)^(2*U):=
    (div_le_div_of_nonneg_right am (R.family.S.a_pos _).le).trans old
  obtain ⟨warm',hm,young,gram⟩:=buy m mf msmall
  obtain ⟨_,sv,atK,outer⟩:=buy v (vm.trans mf) old
  have mono:Monotone (age R v):=by
    intro a b ab
    exact add_le_add (add_le_add_right (sub_le_sub_right ((OPE.scale_mono R.family.S).monotone ab) _) _)
      (by exact_mod_cast Nat.sub_le_sub_right ab v)
  have stopped:|age R v m| ≤ (drift R T (2*U)).buy (badge R f):=abs_le.mpr
    ⟨(abs_le.mp sv).1.trans (mono vm),(mono (mf.trans gap.1.le)).trans (abs_le.mp atK).2⟩
  exact ⟨⟨⟨f,m,t,z,B,warm',hm,young,gram⟩,v,stopped,outer⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonIndependentConditionedStoppedRoom
