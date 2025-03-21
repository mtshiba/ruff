import MonacoEditor from "@monaco-editor/react";
import { Theme } from "shared";

export enum SecondaryTool {
  "AST" = "AST",
  "Tokens" = "Tokens",
}

export type SecondaryPanelResult =
  | null
  | { status: "ok"; content: string }
  | { status: "error"; error: string };

export interface SecondaryPanelProps {
  tool: SecondaryTool;
  result: SecondaryPanelResult;
  theme: Theme;
}

export default function SecondaryPanel({
  tool,
  result,
  theme,
}: SecondaryPanelProps) {
  return (
    <div className="flex flex-col h-full">
      <div className="flex-grow">
        <Content tool={tool} result={result} theme={theme} />
      </div>
    </div>
  );
}

function Content({
  tool,
  result,
  theme,
}: {
  tool: SecondaryTool;
  result: SecondaryPanelResult;
  theme: Theme;
}) {
  if (result == null) {
    return "";
  } else {
    let language;
    switch (result.status) {
      case "ok":
        switch (tool) {
          case "AST":
            language = "RustPythonAst";
            break;

          case "Tokens":
            language = "RustPythonTokens";
            break;
        }

        return (
          <MonacoEditor
            options={{
              readOnly: true,
              minimap: { enabled: false },
              fontSize: 14,
              roundedSelection: false,
              scrollBeyondLastLine: false,
              contextmenu: false,
            }}
            language={language}
            value={result.content}
            theme={theme === "light" ? "Ayu-Light" : "Ayu-Dark"}
          />
        );
      case "error":
        return <code className="whitespace-pre-wrap">{result.error}</code>;
    }
  }
}
