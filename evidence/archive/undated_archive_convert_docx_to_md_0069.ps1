#!/usr/bin/env pwsh
# Convert all .docx files to .md in the previous-research directory

Write-Host "Starting DOCX to Markdown conversion..." -ForegroundColor Green
Write-Host ""

# Define the directory
$targetDir = Join-Path $PSScriptRoot "previous-research"

# Check if directory exists
if (-not (Test-Path $targetDir)) {
    Write-Host "Error: Directory not found: $targetDir" -ForegroundColor Red
    exit 1
}

# Get all .docx files
$docxFiles = Get-ChildItem -Path $targetDir -Filter "*.docx"

if ($docxFiles.Count -eq 0) {
    Write-Host "No .docx files found in $targetDir" -ForegroundColor Yellow
    exit 0
}

Write-Host "Found $($docxFiles.Count) .docx file(s) to convert:" -ForegroundColor Cyan
foreach ($f in $docxFiles) {
    Write-Host "  - $($f.Name)"
}
Write-Host ""

# Counter for tracking
$successCount = 0
$failCount = 0

# Convert each file
foreach ($file in $docxFiles) {
    $inputPath = $file.FullName
    $outputPath = Join-Path $targetDir ($file.BaseName + ".md")
    
    Write-Host "Converting: $($file.Name)" -ForegroundColor White
    
    try {
        # Run pandoc conversion
        $result = & pandoc $inputPath --from=docx --to=markdown --wrap=none --standalone -o $outputPath 2>&1
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "  SUCCESS: Converted to $($file.BaseName).md" -ForegroundColor Green
            $successCount++
            
            if (Test-Path $outputPath) {
                $size = (Get-Item $outputPath).Length
                $sizeKB = [math]::Round($size / 1KB, 2)
                Write-Host "    File size: $sizeKB KB" -ForegroundColor Gray
            }
        }
        else {
            Write-Host "  FAILED: Could not convert file" -ForegroundColor Red
            Write-Host "    Error: $result" -ForegroundColor Red
            $failCount++
        }
    }
    catch {
        Write-Host "  ERROR: $_" -ForegroundColor Red
        $failCount++
    }
    
    Write-Host ""
}

# Summary
Write-Host ("=" * 60) -ForegroundColor Cyan
Write-Host "Conversion Complete!" -ForegroundColor Green
Write-Host "Successfully converted: $successCount file(s)" -ForegroundColor Green
if ($failCount -gt 0) {
    Write-Host "Failed to convert: $failCount file(s)" -ForegroundColor Red
}

Write-Host ""
Write-Host "All markdown files are saved in:" -ForegroundColor Cyan
Write-Host $targetDir -ForegroundColor White