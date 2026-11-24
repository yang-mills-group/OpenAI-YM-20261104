import YM.OPE.Compatible.Streams.Run
/-! # pullback. any discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d k i j m s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w' wV:V→ℝ}{r t:ℕ→ℝ}{Y:V→Mints E→L[ℝ] Mints E}
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][∀ i,FiniteDimensional ℝ (G i)]
namespace Aeon
variable (F:Aeon V T X w')(K:∀ i,i<d→ Eave L X T a (r i) (t i) u i)(P:∀ i:ℕ,i<d → 0<μ i)
variable (G':1 ≤ wV)(C:Wealth w' wV 1)(hp:Wealth Y wV 1)(h:March T Y m)
local notation "Z!"=> extensionV F K P wV G' C hp h
variable (Z:Mints E→L[ℝ] Mints E)(z:ℕ)(ht:Z*X=X*Z)(he:z<d)(i':V) -- Z argument uses S! with free variable maybe type.
lemma flavorStep (hq:∀ p:F.flag z i',∃ x:F.flag z i',x.val=Z p.val ∧ F.read z he i' x=Fellow Z X (μ z) ht (F.read z he i' p))(p:(extensionV F K P wV G' C hp h|>.flag z i'))(hY:Y i' (Z p.val)= Z (Y i' p.val)):
    ∃ t:(extensionV F K P wV G' C hp h|>.flag z i'),t.val=Z p.val ∧ (extensionV F K P wV G' C hp h|>.read z he i' t)=Fellow Z X (μ z) ht ((extensionV F K P wV G' C hp h|>.read z he i') p):=by
        let A:=Z!; let x:= F.picture z Y i' p; let U:=F.read z he i'; let Q:= Fellow Z X (μ z) ht
        obtain ⟨y,hv,hp⟩:=hq x; have he': Z p.val∈A.flag z i':=by change Y i' (Z p.val)∈ F.flag z i'; rw [hY, ← show y.val=Z (Y i' p.val) from hv]; exact y.property
        let p':A.flag z i':=⟨_,he'⟩; refine ⟨p',rfl,?_⟩; let T:=Fleet X (μ z) s (P z he)^m; change T (U (F.picture _ _ i' p'))=Q (T (U x)); rw [show F.picture _ _ _ p'=y from Subtype.ext (hY.trans hv.symm), show U y= Q (U x) from hp]; exact shiftsA _ _ ht _
lemma transF (U W:ℕ→Mints E→Mints E→ ℝ)(J:Fruition X (μ z)→ Fruition X (μ z)→ℝ)(p q:(extensionV F K P wV G' C hp h).flag z i')
    (hZ:Thick (μ z * μ z) (fun i=>U (i+m) p.val q.val-W i (Y i' p.val) (Y i' q.val)))
    (hx:let p':=picture F z Y i' p; let q':= picture F z Y i' q; Thick (μ z*μ z) (fun i=> W i p'.val q'.val-J ((portC X (μ z) s^i) ((F.read z he i') p')) ((portC X (μ z) s^i) ((F.read z he i') q')))):
    let R:= (extensionV F K P wV G' C hp h).read z he i'; Thick (μ z*μ z) (fun i=> U i p.val q.val-J ((portC X (μ z) s^i) (R p)) ((portC X (μ z) s^i) (R q))) :=by
         let f(i):=U (i+m) p.val q.val; let T(i):=W i (Y i' p.val) (Y i' q.val); let N:= (F.read z he i'); let u:=N (picture F z Y i' p); let v:=N (picture F z Y i' q); let L:=portC X (μ z) s; let G':=Fleet X (μ z) s (P z he)^m; let g(i:ℕ):= J ((L^i) u) ((L^i) v); intro R; apply parkT m; change Thick _ (fun i=> f i - J ((L^(i+m)) (G' u)) ((L^(i+m)) (G' v))); rw [show (fun i:ℕ=>f i-_)=(fun i=>f i-J ((L^i) u) ((L^i) v)) from funext fun i=> congrArg (fun x=> f i-x) (congr_arg₂ J (powerB ..) (powerB ..))]; change Thick _ (f-g); rw [show f-g=(f-T)+(T-g) by abel]; exact Thick.add hZ hx
end Aeon
end YM.OPE.Hark
