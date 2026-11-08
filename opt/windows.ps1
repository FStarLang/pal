[CmdletBinding()]
param(
    [string]$MsysRoot = $env:PAL_MSYS_ROOT,
    [string]$FStarRoot = $env:PAL_FSTAR_ROOT,
    [string[]]$Command = @()
)

$ErrorActionPreference = 'Stop'
if (-not $IsWindows) {
    throw 'This launcher requires PowerShell 7 on Windows.'
}
if (-not $MsysRoot -or -not $FStarRoot) {
    throw 'Specify -MsysRoot and -FStarRoot, or set PAL_MSYS_ROOT and PAL_FSTAR_ROOT.'
}
$bash = Join-Path $MsysRoot 'usr\bin\bash.exe'
$fstar = Join-Path $FStarRoot 'bin\fstar.exe'
foreach ($file in @($bash, $fstar)) {
    if (-not (Test-Path -LiteralPath $file -PathType Leaf)) {
        throw "Required executable not found: $file"
    }
}
$repoRoot = Split-Path $PSScriptRoot -Parent
$script = @'
set -euo pipefail
export PATH="$(cygpath -u "$1")/bin:$PATH"
cd "$(cygpath -u "$2")"
shift 2
if (( $# )); then
    exec "$@"
fi
exec bash --noprofile --norc -i
'@
$startInfo = [System.Diagnostics.ProcessStartInfo]::new($bash)
$startInfo.UseShellExecute = $false
$startInfo.WorkingDirectory = $repoRoot
$startInfo.Environment['MSYSTEM'] = 'UCRT64'
$startInfo.Environment['MSYS'] = 'winsymlinks:nativestrict'
$startInfo.Environment['CHERE_INVOKING'] = '1'
foreach ($argument in @('--login', '-c', $script, 'pal-windows', $FStarRoot, $repoRoot) + $Command) {
    $startInfo.ArgumentList.Add($argument)
}
$process = [System.Diagnostics.Process]::Start($startInfo)
try {
    $process.WaitForExit()
    $code = $process.ExitCode
}
finally {
    $process.Dispose()
}
exit $code
