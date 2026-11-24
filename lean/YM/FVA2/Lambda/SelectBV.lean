import YM.FVA2.Lambda.Pad
/-!
# d=4 vertex (closed net or unrestricted), simplification table by ghost number

 Keep k-pairing Koszul external for unequal parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Area
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Complex (I)
open Canvas (quad high top_quad line4 triple upperquad trigger)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))

variable (a b c:Axis)(k l j:G.ColorIndex)(p q r:QP)
lemma boolW_h : parity (W₀ a k)=false:= rfl
lemma boolW : Ψ (W₀ a k,p)=false:= rfl
lemma boolC_h : parity (C₀ k)=true:= rfl
lemma boolC : Ψ (C₀ k,p)=true:= rfl
lemma boolU_h : parity (U₀ a k)=true:= rfl
lemma boolU : Ψ (U₀ a k,p)=true:= rfl
lemma boolS_h : parity (S₀ k)=false:= rfl
lemma boolS : Ψ (S₀ k,p)=false:= rfl
lemma at_WWW : triple G [(W₀ a k,p), (W₀ b l,q), (W₀ c j,r)]=I*rune k l j*( Slice.rib a b c p q r:ℂ ):= Slice.t_WWW ..
lemma at_WWC : triple G [(W₀ a k,p), (W₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((0:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_WWU : triple G [(W₀ a k,p), (W₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((0:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_WWS : triple G [(W₀ a k,p), (W₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((0:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_WCW : triple G [(W₀ a k,p), (C₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_WCC : triple G [(W₀ a k,p), (C₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_WCU : triple G [(W₀ a k,p), (C₀ l,q), (U₀ c j,r)]=-(rune k l j)*(Slice.delta c a:ℂ):= Slice.t_WCU ..
lemma at_WCS : triple G [(W₀ a k,p), (C₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_WUW : triple G [(W₀ a k,p), (U₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_WUC : triple G [(W₀ a k,p), (U₀ b l,q), (C₀ j,r)]=(rune k j l)*(Slice.delta b a:ℂ):= Slice.t_WUC ..
lemma at_WUU : triple G [(W₀ a k,p), (U₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_WUS : triple G [(W₀ a k,p), (U₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_WSW : triple G [(W₀ a k,p), (S₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-2:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_WSC : triple G [(W₀ a k,p), (S₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-2:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_WSU : triple G [(W₀ a k,p), (S₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-2:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_WSS : triple G [(W₀ a k,p), (S₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (0:ℤ) + ((-2:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_CWW : triple G [(C₀ k,p), (W₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((0:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_CWC : triple G [(C₀ k,p), (W₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((0:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_CWU : triple G [(C₀ k,p), (W₀ b l,q), (U₀ c j,r)]=-(rune l k j)*(Slice.delta c b:ℂ):= Slice.t_CWU ..
lemma at_CWS : triple G [(C₀ k,p), (W₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((0:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_CCW : triple G [(C₀ k,p), (C₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_CCC : triple G [(C₀ k,p), (C₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_CCU : triple G [(C₀ k,p), (C₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_CCS : triple G [(C₀ k,p), (C₀ l,q), (S₀ j,r)]=rune k l j:= Slice.t_CCS ..
lemma at_CUW : triple G [(C₀ k,p), (U₀ b l,q), (W₀ c j,r)]=-(rune j k l)*(Slice.delta b c:ℂ):= Slice.t_CUW ..
lemma at_CUC : triple G [(C₀ k,p), (U₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_CUU : triple G [(C₀ k,p), (U₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_CUS : triple G [(C₀ k,p), (U₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_CSW : triple G [(C₀ k,p), (S₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-2:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_CSC : triple G [(C₀ k,p), (S₀ l,q), (C₀ j,r)]=rune k j l:= Slice.t_CSC ..
lemma at_CSU : triple G [(C₀ k,p), (S₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-2:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_CSS : triple G [(C₀ k,p), (S₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (1:ℤ) + ((-2:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_UWW : triple G [(U₀ a k,p), (W₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((0:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_UWC : triple G [(U₀ a k,p), (W₀ b l,q), (C₀ j,r)]=(rune l j k)*(Slice.delta a b:ℂ):= Slice.t_UWC ..
lemma at_UWU : triple G [(U₀ a k,p), (W₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((0:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_UWS : triple G [(U₀ a k,p), (W₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((0:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_UCW : triple G [(U₀ a k,p), (C₀ l,q), (W₀ c j,r)]=(rune j l k)*(Slice.delta a c:ℂ):= Slice.t_UCW ..
lemma at_UCC : triple G [(U₀ a k,p), (C₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_UCU : triple G [(U₀ a k,p), (C₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_UCS : triple G [(U₀ a k,p), (C₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_UUW : triple G [(U₀ a k,p), (U₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_UUC : triple G [(U₀ a k,p), (U₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_UUU : triple G [(U₀ a k,p), (U₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_UUS : triple G [(U₀ a k,p), (U₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_USW : triple G [(U₀ a k,p), (S₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-2:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_USC : triple G [(U₀ a k,p), (S₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-2:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_USU : triple G [(U₀ a k,p), (S₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-2:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_USS : triple G [(U₀ a k,p), (S₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-1:ℤ) + ((-2:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_SWW : triple G [(S₀ k,p), (W₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((0:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_SWC : triple G [(S₀ k,p), (W₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((0:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_SWU : triple G [(S₀ k,p), (W₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((0:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_SWS : triple G [(S₀ k,p), (W₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((0:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_SCW : triple G [(S₀ k,p), (C₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_SCC : triple G [(S₀ k,p), (C₀ l,q), (C₀ j,r)]=rune l j k:= Slice.t_SCC ..
lemma at_SCU : triple G [(S₀ k,p), (C₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_SCS : triple G [(S₀ k,p), (C₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_SUW : triple G [(S₀ k,p), (U₀ b l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-1:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_SUC : triple G [(S₀ k,p), (U₀ b l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-1:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_SUU : triple G [(S₀ k,p), (U₀ b l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-1:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_SUS : triple G [(S₀ k,p), (U₀ b l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-1:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )
lemma at_SSW : triple G [(S₀ k,p), (S₀ l,q), (W₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-2:ℤ) + ((0:ℤ) + 0 ))≠0; decide )
lemma at_SSC : triple G [(S₀ k,p), (S₀ l,q), (C₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-2:ℤ) + ((1:ℤ) + 0 ))≠0; decide )
lemma at_SSU : triple G [(S₀ k,p), (S₀ l,q), (U₀ c j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-2:ℤ) + ((-1:ℤ) + 0 ))≠0; decide )
lemma at_SSS : triple G [(S₀ k,p), (S₀ l,q), (S₀ j,r)]=0:= Slice.tghost _ (by change (-2:ℤ) + ((-2:ℤ) + ((-2:ℤ) + 0 ))≠0; decide )

/- Reuse with `simp` linter explicitly disabled in files Cherry & Indigo due to long common list. Keeps tensor expressions unexpanded. Does not drop a rung because geometry. -/
macro "triples_core" : tactic => `(tactic| simp only [cross_false,cross_false', Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true,cross_true, degree_cons, degree_nil,boolW,boolW_h,boolC,boolC_h,boolU,boolU_h,boolS,boolS_h, at_WWW, at_WWC, at_WWU, at_WWS, at_WCW, at_WCC, at_WCU, at_WCS, at_WUW, at_WUC, at_WUU, at_WUS, at_WSW, at_WSC, at_WSU, at_CWW, at_CWC, at_CWU, at_CWS, at_CCW, at_CCC, at_CCU, at_CCS, at_CUW, at_CUC, at_CUU, at_CUS, at_CSW, at_CSC, at_CSU, at_UWW, at_UWC, at_UWU, at_UWS, at_UCW, at_UCC, at_UCU, at_UCS, at_UUW, at_UUC, at_UUU, at_UUS, at_USW, at_USC, at_USU, at_SWW, at_SWC, at_SWU, at_SCW, at_SCC, at_SCU, at_SUW, at_SUC, at_SUU,one_mul,neg_one_mul, mul_zero, zero_mul, zero_add, add_zero, neg_zero, Finset.sum_const_zero,neg_neg ])
end YM.FVA2.Lambda.Area

